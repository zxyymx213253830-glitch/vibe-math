"""Bind actual full-rank, energy and support leaf checks to reviewed sources."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PROJECT = ROOT/'theory/jin_wishart_formalization'
BASE = PROJECT/'JinWishartFormalization'
LIB = ROOT/'.tools/publication-revision-20261016/fresh-project-library'
TARGETS = [('GaussianGramFullRank', 'full-rank-3.txt', 9),
           ('GaussianGramEnergyLaw', 'energy-law-2.txt', 6),
           ('GaussianGramSupport', 'support-1.txt', 9)]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    request = json.loads((HERE/'review-request.json').read_text(encoding='utf-8'))
    assert request['prompt_sha256'] == sha(HERE/'p4-prompt.txt')
    results = {}
    for name, logname, count in TARGETS:
        path = BASE/(name+'.lean')
        body = path.read_text(encoding='utf-8', errors='strict')
        stripped = re.sub(r'/\-.*?\-/', '', body, flags=re.S)
        stripped = re.sub(r'--[^\n]*', '', stripped)
        stripped = re.sub(r'^#print axioms.*$', '', stripped, flags=re.M)
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', stripped)
        log = HERE/logname
        diagnostic = log.read_text(encoding='utf-8')
        assert 'error:' not in diagnostic and 'sorryAx' not in diagnostic
        names = re.findall(r'^(?:theorem|instance)\s+(\w+)', body, flags=re.M)
        assert len(names) == count
        entries = []
        for item in names:
            qualified = 'JinWishart.'+item
            found = re.search(re.escape("'"+qualified+"' depends on axioms:")+
                              r'\s*\[([^\]]*)\]', diagnostic)
            assert found, qualified
            axioms = set(x.strip() for x in found[1].split(','))
            assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}
            entries.append(dict(name=qualified, axioms=sorted(axioms), author='Codex'))
        artifact = LIB/'JinWishartFormalization'/(name+'.olean')
        assert artifact.stat().st_mtime >= path.stat().st_mtime
        assert log.stat().st_mtime >= path.stat().st_mtime
        assert request['inputs'][path.name]['sha256'] == sha(path)
        assert sha(HERE/'review-snapshot'/path.name) == sha(path)
        deps = {}
        for module in re.findall(r'^import\s+([\w.]+)', body, flags=re.M):
            rel = Path(module.replace('.', '/')+'.olean')
            choices = [LIB/rel] + [p/'.lake/build/lib/lean'/rel
                for p in (PROJECT/'.lake/packages').iterdir() if p.is_dir()]
            selected = next((p for p in choices if p.exists()), None)
            assert selected, module
            deps[module] = dict(path=selected.relative_to(ROOT).as_posix(), sha256=sha(selected))
        results[name] = dict(declarations=entries, source_sha256=sha(path), log_sha256=sha(log),
            olean_sha256=sha(artifact), kernel_exit_code=0, direct_imports=deps)
    support = BASE/'ComplexGramSimpleSpectrum.lean'
    assert request['inputs'][support.name]['sha256'] == sha(support)
    control = json.loads((HERE/'control.json').read_text(encoding='utf-8'))
    assert control['seed'] == 20261017 and len(control['records']) == 4
    assert control['source_sha256'] == sha(ROOT/'experiments/gaussian_full_rank_control.py')
    for row in control['records']:
        assert row['N'] == 200000 and abs(row['trace_standard_errors']) < 6
        assert abs(row['logdet_standard_errors']) < 6
    raw = json.loads((HERE/'p4.raw.json').read_text(encoding='utf-8'))
    receipt = json.loads((HERE/'p4.receipt.json').read_text(encoding='utf-8'))
    assert receipt['exit_code'] == 0 and not raw['is_error']
    assert receipt['prompt_sha256'] == request['prompt_sha256']
    assert receipt['runner_sha256'] == sha(ROOT/'tools/partners/qoder_request.py')
    assert 'qmodel_38max' in raw['modelUsage']
    assert (HERE/'p4.response.md').read_text(encoding='utf-8').strip() == raw['result'].strip()
    for failure in ['full-rank-1.txt', 'full-rank-2.txt', 'energy-law-1.txt']:
        assert 'error:' in (HERE/failure).read_text(encoding='utf-8')
    report = dict(collected_utc=datetime.now(timezone.utc).isoformat(), targets=results,
        total_declarations=24, actual_gaussian_full_rank='PROVED for n<=m, any fixed mean',
        smaller_side_positive_definite='PROVED every rectangular shape, any fixed mean',
        actual_preceding_matrix_energy_product='PROVED for 0<n<m, fresh independent central Gaussian',
        convention='Fresh stdGaussian complex column has real-coordinate variance1; energies divide by2',
        general_matrix_density_and_G2='OPEN', joint_Bartlett_matrix_law='OPEN',
        review='Actual Qoder/Qwen3.8-Max model-only P4, supplied target sources and specified excerpts',
        human_review='REQUIRED: inherited Fubini/null-set, variance/model correspondence',
        toolchain=(PROJECT/'lean-toolchain').read_text().strip(),
        dependency_manifest_sha256=sha(PROJECT/'lake-manifest.json'),
        facade_and_full_build='NOT_RUN', publication='UNCHANGED',
        evidence={p.relative_to(HERE).as_posix():sha(p) for p in HERE.rglob('*')
            if p.is_file() and p.name != 'audit.json' and '__pycache__' not in p.parts},
        status='PASS 24 declarations, standard axioms, controls, source/artifact/review bindings')
    (HERE/'audit.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print('PASS 24 actual full-rank/support/energy declarations; hashes and scoped model review verified.')


if __name__ == '__main__':
    main()
