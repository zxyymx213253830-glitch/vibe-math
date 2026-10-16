"""Audit the actual new-leaf and integration outputs, not an external review."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
PROJECT = ROOT / 'theory/jin_wishart_formalization'
LIBRARY = ROOT / '.tools/publication-revision-20261016/fresh-project-library'
MODULE = 'JinWishartFormalization.GaussianGramProjector'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_only(text):
    # The audited new files contain no nested block comments or string literals.
    text = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    return re.sub(r'^#print axioms.*$', '', text, flags=re.M)


def main():
    source = PROJECT / Path(MODULE.replace('.', '/') + '.lean')
    body = source.read_text(encoding='utf-8', errors='strict')
    log = HERE / 'gram-projector-final.txt'
    diagnostic = log.read_text(encoding='utf-8')
    assert 'error:' not in diagnostic and 'sorryAx' not in diagnostic
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', code_only(body))
    names = re.findall(r'^theorem\s+(\w+)', body, flags=re.M)
    assert len(names) == 11
    declarations = []
    for name in names:
        qualified = 'JinWishart.' + name
        found = re.search(re.escape("'" + qualified + "' depends on axioms:") +
                          r'\s*\[([^\]]*)\]', diagnostic)
        assert found, name
        axioms = set(x.strip() for x in found[1].split(','))
        assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}
        declarations.append(dict(name=qualified, axioms=sorted(axioms), author='Codex'))
    compiled = LIBRARY / Path(MODULE.replace('.', '/') + '.olean')
    assert compiled.exists() and compiled.stat().st_mtime >= source.stat().st_mtime
    assert log.stat().st_mtime >= source.stat().st_mtime
    integration = HERE / 'GramProjectorIntegration.lean'
    ibody = integration.read_text(encoding='utf-8', errors='strict')
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', code_only(ibody))
    ilog = HERE / 'integration-check.txt'
    assert 'error:' not in ilog.read_text(encoding='utf-8')
    icompiled = LIBRARY / 'GramProjectorIntegration.olean'
    assert icompiled.exists() and icompiled.stat().st_mtime >= integration.stat().st_mtime
    experiment = ROOT / 'experiments/gram_inverse_projector_control.py'
    preflight = json.loads((HERE/'gram-projector-preflight.json').read_text(encoding='utf-8'))
    assert preflight['source_sha256'] == sha(experiment)
    assert preflight['seed'] == 20261016 and len(preflight['records']) == 3
    for call in ['invocation.json', 'invocation-2.json']:
        assert json.loads((HERE/call).read_text(encoding='utf-8'))['exit_code'] == 124
    assert not (HERE/'response.json').read_bytes()
    assert not (HERE/'response-2.json').read_bytes()
    # These exact files were supplied to the unsuccessful review calls.
    request = json.loads((HERE/'request-manifest.json').read_text(encoding='utf-8'))
    for path, digest in request['inputs'].items():
        assert sha(ROOT/path) == digest
    assert hashlib.sha256((HERE/'p4-prompt.txt').read_text(
        encoding='utf-8').encode('utf-8')).hexdigest() == request['prompt_sha256']
    assert sha(HERE/'p4-prompt.txt') == request['prompt_file_sha256']

    # Bind direct compiled imports from the actual selected library paths.
    deps = {}
    for module in re.findall(r'^import\s+([\w.]+)', body, flags=re.M) + [
            'JinWishartFormalization.GaussianRandomSubspaceLaw']:
        rel = Path(module.replace('.', '/') + '.olean')
        matches = [LIBRARY/rel] + [p/'.lake/build/lib/lean'/rel
            for p in (PROJECT/'.lake/packages').iterdir() if p.is_dir()]
        selected = next((p for p in matches if p.exists()), None)
        assert selected, module
        deps[module] = dict(path=selected.relative_to(ROOT).as_posix(), sha256=sha(selected),
                            use='Existing cache, not recompiled by this audit')
    result = dict(collected_utc=datetime.now(timezone.utc).isoformat(),
        declarations=declarations, source_sha256=sha(source), log_sha256=sha(log),
        olean_sha256=sha(compiled), direct_import_cache_bindings=deps,
        integration=dict(source_sha256=sha(integration), olean_sha256=sha(icompiled),
                         log_sha256=sha(ilog), scope='Interface example, not a new Wishart theorem'),
        toolchain=(PROJECT/'lean-toolchain').read_text().strip(),
        dependency_manifest_sha256=sha(PROJECT/'lake-manifest.json'),
        evidence={p.name:sha(p) for p in HERE.iterdir()
                  if p.is_file() and p.name != 'audit.json'},
        external_review='NOT_COMPLETED: two CLI timeouts, no usable response',
        external_backend_model='Unconfirmed; no response metadata received',
        pending='Independent P4/human review, Gaussian full-rank probability and dimensions, general Jacobian/density/G2',
        scope='New leaf and explicit integration example; no facade/full-build or publication refresh',
        status='PASS eleven kernel/standard-axiom checks, integration and source bindings')
    (HERE/'audit.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print('PASS 11 declarations; integration and input/artifact hashes verified. P4 remains incomplete.')


if __name__ == '__main__':
    main()
