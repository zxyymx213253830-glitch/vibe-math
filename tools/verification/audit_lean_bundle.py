"""Audit a declared Lean leaf bundle and bind controls and model-review snapshots.

This reads real compiler logs/artifacts; it does not compile or perform human review.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT/'theory/jin_wishart_formalization'
SOURCE_ROOT = PROJECT/'JinWishartFormalization'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--spec', required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    spec_path = (ROOT/args.spec).resolve()
    spec = json.loads(spec_path.read_text(encoding='utf-8'))
    library = ROOT/spec['library']
    modules = {}
    total = 0
    for target in spec['targets']:
        module = target['module']
        relative = Path(module.replace('.', '/'))
        source = PROJECT/relative.with_suffix('.lean')
        compiled = library/relative.with_suffix('.olean')
        log = ROOT/target['log']
        body = source.read_text(encoding='utf-8', errors='strict')
        # Bundle sources use ordinary non-nested doc comments and no string literals.
        code = re.sub(r'/\-.*?\-/', '', body, flags=re.S)
        code = re.sub(r'--[^\n]*', '', code)
        code = re.sub(r'^#print axioms.*$', '', code, flags=re.M)
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', code), module
        names = re.findall(r'^(?:theorem|instance)\s+(\w+)', body, flags=re.M)
        assert len(names) == target['count'], (module, names)
        witnesses = target.get('witnesses', [])
        for witness in witnesses:
            assert re.search(r'^def\s+'+re.escape(witness)+r'\b', body, flags=re.M), witness
            assert witness not in names
            names.append(witness)
        diagnostic = log.read_text(encoding='utf-8')
        assert 'error:' not in diagnostic and 'sorryAx' not in diagnostic, module
        entries = []
        for name in names:
            qualified = 'JinWishart.'+name
            found = re.search(re.escape("'"+qualified+"' depends on axioms:")+
                r'\s*\[([^\]]*)\]', diagnostic)
            no_axioms = "'"+qualified+"' does not depend on any axioms" in diagnostic
            assert found or no_axioms, qualified
            axioms = set(s.strip() for s in found[1].split(',') if s.strip()) if found else set()
            assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, qualified
            entries.append(dict(name=qualified, axioms=sorted(axioms), author='Codex',
                                kind='constructed witness' if name in witnesses else 'theorem or instance'))
        assert compiled.exists() and compiled.stat().st_mtime >= source.stat().st_mtime, module
        assert log.stat().st_mtime >= source.stat().st_mtime, module
        assert target['kernel_exit_code_recorded'] == 0
        imports = {}
        for dep in re.findall(r'^import\s+([\w.]+)', body, flags=re.M):
            dep_rel = Path(dep.replace('.', '/')+'.olean')
            candidates = [library/dep_rel] + [p/'.lake/build/lib/lean'/dep_rel
                for p in (PROJECT/'.lake/packages').iterdir() if p.is_dir()]
            selected = next((p for p in candidates if p.exists()), None)
            assert selected, dep
            imports[dep] = dict(path=selected.relative_to(ROOT).as_posix(), sha256=sha(selected))
        modules[module] = dict(declarations=entries, source_sha256=sha(source),
            olean_sha256=sha(compiled), log_sha256=sha(log), imports=imports)
        total += len(entries)
    controls = []
    for item in spec.get('controls', []):
        script, result = ROOT/item['script'], ROOT/item['result']
        data = json.loads(result.read_text(encoding='utf-8'))
        assert data['source_sha256'] == sha(script)
        assert data['seed'] == item['seed'] and data['status'].startswith('PASS')
        controls.append(dict(script=item['script'], script_sha256=sha(script), result_sha256=sha(result),
                             interpretation='Reproducible control, not a proof'))
    reviews = []
    for item in spec.get('reviews', []):
        request = json.loads((ROOT/item['request']).read_text(encoding='utf-8'))
        prompt = ROOT/item['prompt']
        receipt = json.loads((ROOT/item['receipt']).read_text(encoding='utf-8'))
        raw_path = ROOT/item['raw']
        provider = item.get('provider', 'qoder')
        if provider == 'claude':
            events = [json.loads(line) for line in raw_path.read_text(encoding='utf-8').splitlines()
                      if line.strip()]
            raw = next(event for event in reversed(events) if event.get('type') == 'result')
            runner = ROOT/'tools/partners/claude_review.py'
            reported_models = list(raw.get('modelUsage', {})) or receipt.get('reported_models', [])
        else:
            assert provider == 'qoder', provider
            raw = json.loads(raw_path.read_text(encoding='utf-8'))
            runner = ROOT/'tools/partners/qoder_request.py'
            reported_models = list(raw.get('modelUsage', {}))
        assert request['prompt_sha256'] == sha(prompt) == receipt['prompt_sha256']
        assert receipt['exit_code'] == 0 and not raw['is_error']
        assert receipt['runner_sha256'] == sha(runner)
        source_changes = []
        for name, record in request['inputs'].items():
            current_sha = sha(SOURCE_ROOT/name)
            if record['sha256'] != current_sha:
                assert name in item.get('allow_changed_sources', []), name
                source_changes.append(dict(source=name, reviewed_sha256=record['sha256'],
                    current_sha256=current_sha, final_source_reviewed=False))
            if record.get('supplied') == 'Full source':
                assert record['sha256'] == sha(ROOT/item['snapshot']/name)
        reviews.append(dict(request_sha256=sha(ROOT/item['request']), prompt_sha256=sha(prompt),
            raw_response_sha256=sha(raw_path), provider=provider, reported_models=reported_models,
            independent_compilation=False, human_review=False, source_changes=source_changes))
    report = dict(collected_utc=datetime.now(timezone.utc).isoformat(), spec_sha256=sha(spec_path),
        auditor_sha256=sha(Path(__file__)), modules=modules, total_declarations=total,
        controls=controls, reviews=reviews, scope=spec['scope'],
        human_review='REQUIRED for stated measure/model interpretation',
        full_build='NOT_RUN', paper_and_submission='UNCHANGED',
        toolchain=(PROJECT/'lean-toolchain').read_text().strip(),
        lake_manifest_sha256=sha(PROJECT/'lake-manifest.json'), status='PASS specified leaf bundle and bindings')
    target = ROOT/args.output
    target.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(f'PASS {total} declarations; source/artifact/log/control/review bindings.')


if __name__ == '__main__':
    main()
