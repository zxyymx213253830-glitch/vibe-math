"""Validate this milestone's kernel, source, controls and review bindings."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PROJECT = ROOT/'theory/jin_wishart_formalization'
LIBRARY = ROOT/'.tools/publication-revision-20261016/fresh-project-library'
MODULE = 'JinWishartFormalization.GaussianGramDimensions'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source = PROJECT/Path(MODULE.replace('.', '/')+'.lean')
    text = source.read_text(encoding='utf-8', errors='strict')
    stripped = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    stripped = re.sub(r'--[^\n]*', '', stripped)
    stripped = re.sub(r'^#print axioms.*$', '', stripped, flags=re.M)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', stripped)
    log = HERE/'gram-dimensions-4.txt'
    diagnostic = log.read_text(encoding='utf-8')
    assert 'error:' not in diagnostic and 'sorryAx' not in diagnostic
    names = re.findall(r'^theorem\s+(\w+)', text, flags=re.M)
    assert len(names) == 7
    declarations = []
    for name in names:
        qualified = 'JinWishart.'+name
        found = re.search(re.escape("'"+qualified+"' depends on axioms:")+
                          r'\s*\[([^\]]*)\]', diagnostic)
        assert found, name
        axioms = set(x.strip() for x in found[1].split(','))
        assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}
        declarations.append(dict(name=qualified, axioms=sorted(axioms), author='Codex'))
    compiled = LIBRARY/Path(MODULE.replace('.', '/')+'.olean')
    assert compiled.exists() and compiled.stat().st_mtime >= source.stat().st_mtime
    assert log.stat().st_mtime >= source.stat().st_mtime
    for i in (1, 2, 3):
        failure = (HERE/f'gram-dimensions-{i}.txt').read_text(encoding='utf-8')
        assert 'error:' in failure
    controls = json.loads((HERE/'rank-control.json').read_text(encoding='utf-8'))
    experiment = ROOT/'experiments/gram_real_dimension_control.py'
    assert controls['source_sha256'] == sha(experiment)
    assert controls['seed'] == 20261017 and len(controls['records']) == 5
    for row in controls['records']:
        assert row['complex_rank'] == row['n']
        assert row['real_rank'] == 2*row['n']
        assert row['orthogonal_dimension'] == 2*(row['m']-row['n'])

    reviews = {}
    for name, request_name in [('p4', 'review-request.json'),
                               ('p4-final', 'p4-final-request.json'),
                               ('p4-checked', 'p4-checked-request.json')]:
        request = json.loads((HERE/request_name).read_text(encoding='utf-8'))
        assert request['prompt_sha256'] == sha(HERE/(name+'-prompt.txt'))
        for path, digest in request['inputs'].items():
            snapshot = HERE/(name+'-snapshot')/Path(path).name
            assert sha(snapshot) == digest
            if name == 'p4-checked':
                assert sha(ROOT/path) == digest
        raw = json.loads((HERE/(name+'.stdout.json')).read_text(encoding='utf-8'))
        receipt = json.loads((HERE/(name+'-result.json')).read_text(encoding='utf-8'))
        assert raw['type'] == 'result' and not raw['is_error']
        assert receipt['exit_code'] == 0 and 'qmodel_38max' in raw['modelUsage']
        (HERE/(name+'-response.md')).write_text(raw['result']+'\n', encoding='utf-8')
        reviews[name] = dict(raw_sha256=sha(HERE/(name+'.stdout.json')),
                            prompt_sha256=request['prompt_sha256'],
                            backend_label=list(raw['modelUsage']),
                            credits_reported=raw.get('total_credits'),
                            scope=request['scope'])
    route = json.loads((HERE/'rank-route.stdout.json').read_text(encoding='utf-8'))
    (HERE/'rank-route-response.md').write_text(route['result']+'\n', encoding='utf-8')
    assert route['result'] and not route['is_error']
    assert json.loads((HERE/'rank-result.json').read_text(encoding='utf-8'))['exit_code'] == 124
    assert json.loads((HERE/'connection.stdout.json').read_text(encoding='utf-8'))['result'] == 'OK'

    imports = {}
    for module in re.findall(r'^import\s+([\w.]+)', text, flags=re.M):
        rel = Path(module.replace('.', '/')+'.olean')
        candidates = [LIBRARY/rel] + [p/'.lake/build/lib/lean'/rel
            for p in (PROJECT/'.lake/packages').iterdir() if p.is_dir()]
        selected = next((p for p in candidates if p.exists()), None)
        assert selected, module
        imports[module] = dict(path=selected.relative_to(ROOT).as_posix(), sha256=sha(selected),
                               use='Existing compiled dependency, not rebuilt in this milestone')
    report = dict(collected_utc=datetime.now(timezone.utc).isoformat(), declarations=declarations,
        source_sha256=sha(source), log_sha256=sha(log), olean_sha256=sha(compiled),
        experiment_sha256=sha(experiment), control_sha256=sha(HERE/'rank-control.json'),
        direct_imports=imports, toolchain=(PROJECT/'lean-toolchain').read_text().strip(),
        dependency_manifest_sha256=sha(PROJECT/'lake-manifest.json'),
        kernel_exit_code=0, failed_kernel_attempts=3, reviews=reviews,
        review_caveat='Earlier reviews missed real elaboration failures. Final review is model-only, not independent compilation or human review.',
        provenance='Codex proof bodies; Qoder/Qwen3.8-Max P1 route comparison and P4 observations. No local DS proof body in this milestone.',
        actual_gaussian_full_rank='OPEN', general_wishart_density_G2='OPEN', human_review='REQUIRED',
        facade_or_full_build='NOT_RUN', paper_and_release='UNCHANGED',
        evidence={p.relative_to(HERE).as_posix():sha(p) for p in HERE.rglob('*')
                  if p.is_file() and p.name != 'audit.json' and '__pycache__' not in p.parts},
        status='PASS seven kernel declarations, standard axioms, exact controls and final review/source bindings')
    (HERE/'audit.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print('PASS seven declarations; source/olean/log/control/review hashes bound. Human review remains required.')


if __name__ == '__main__':
    main()
