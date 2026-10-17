"""Audit the actual column-append leaf and its supplied-model review."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PROJECT = ROOT/'theory/jin_wishart_formalization'
LIB = ROOT/'.tools/publication-revision-20261016/fresh-project-library'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    name = 'GaussianColumnAppendLaw'
    source = PROJECT/'JinWishartFormalization'/(name+'.lean')
    body = source.read_text(encoding='utf-8', errors='strict')
    code = re.sub(r'/\-.*?\-/', '', body, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    code = re.sub(r'^#print axioms.*$', '', code, flags=re.M)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', code)
    log = HERE/'append-3.txt'
    diagnostic = log.read_text(encoding='utf-8')
    assert 'error:' not in diagnostic and 'sorryAx' not in diagnostic
    names = re.findall(r'^theorem\s+(\w+)', body, flags=re.M)
    assert len(names) == 10
    entries = []
    for item in names:
        qualified = 'JinWishart.'+item
        found = re.search(re.escape("'"+qualified+"' depends on axioms:")+r'\s*\[([^\]]*)\]', diagnostic)
        assert found, qualified
        axioms = set(x.strip() for x in found[1].split(','))
        assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}
        entries.append(dict(name=qualified, axioms=sorted(axioms), author='Codex'))
    compiled = LIB/'JinWishartFormalization'/(name+'.olean')
    assert compiled.stat().st_mtime >= source.stat().st_mtime
    assert log.stat().st_mtime >= source.stat().st_mtime
    request = json.loads((HERE/'review-request.json').read_text(encoding='utf-8'))
    assert request['prompt_sha256'] == sha(HERE/'p4-prompt.txt')
    for file, record in request['inputs'].items():
        actual = PROJECT/'JinWishartFormalization'/file
        assert record['sha256'] == sha(actual)
        if record.get('supplied') == 'Full source':
            assert record['sha256'] == sha(HERE/'review-snapshot'/file)
    raw = json.loads((HERE/'p4.raw.json').read_text(encoding='utf-8'))
    receipt = json.loads((HERE/'p4.receipt.json').read_text(encoding='utf-8'))
    assert receipt['exit_code'] == 0 and not raw['is_error']
    assert receipt['prompt_sha256'] == request['prompt_sha256']
    assert 'qmodel_38max' in raw['modelUsage']
    controls = json.loads((HERE/'control.json').read_text(encoding='utf-8'))
    assert controls['source_sha256'] == sha(ROOT/'experiments/gaussian_column_append_control.py')
    assert controls['inherited_law_control_sha256'] == sha(
        ROOT/'verification/WISHART_RANDOM_SUBSPACE_CONTROL_20261016.json')
    assert controls['seed'] == 20261017 and len(controls['records']) == 4
    for failure in ['append-1.txt', 'append-2.txt']:
        assert 'error:' in (HERE/failure).read_text(encoding='utf-8')
    imports = {module:sha(LIB/Path(module.replace('.', '/')+'.olean'))
               for module in re.findall(r'^import\s+([\w.]+)', body, flags=re.M)}
    result = dict(collected_utc=datetime.now(timezone.utc).isoformat(), declarations=entries,
        source_sha256=sha(source), log_sha256=sha(log), olean_sha256=sha(compiled), imports=imports,
        kernel_exit_code=0, proof_author='Codex', model_review='Qoder/Qwen3.8-Max; no concrete issue in supplied scope',
        review_resolution='Potential index warning resolved by exact previous_apply/fresh_apply rfl identities and final source law. No independent compile by reviewer.',
        human_review='REQUIRED: product/Fubini, indexing/variance and model correspondence',
        general_Bartlett_matrix_law='OPEN; only the actual column energy step is proved',
        facade_and_full_build='NOT_RUN', paper_and_submission='UNCHANGED',
        toolchain=(PROJECT/'lean-toolchain').read_text().strip(),
        dependency_manifest_sha256=sha(PROJECT/'lake-manifest.json'),
        evidence={p.relative_to(HERE).as_posix():sha(p) for p in HERE.rglob('*')
            if p.is_file() and p.name != 'audit.json' and '__pycache__' not in p.parts},
        status='PASS ten declarations and source/artifact/review/control bindings')
    (HERE/'audit.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print('PASS ten actual column-append declarations and scoped review/source bindings.')


if __name__ == '__main__':
    main()
