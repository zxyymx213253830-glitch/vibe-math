"""Bind the new leaf's actual kernel audit to source and cached dependencies.

Does not compile Lean or claim a full build, independent P4, or publication update.
Run after the serialized collaborative_check command documented in README.md.
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re


ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / 'theory/jin_wishart_formalization'
LIBRARY = ROOT / '.tools/publication-revision-20261016/fresh-project-library'
HERE = Path(__file__).resolve().parent
MODULE = 'JinWishartFormalization.GaussianRandomSubspaceLaw'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    log = HERE / 'random-split-1.txt'
    diagnostic = log.read_text(encoding='utf-8')
    assert ': error:' not in diagnostic and 'sorryAx' not in diagnostic
    source_path = PROJECT / Path(MODULE.replace('.', '/') + '.lean')
    source = source_path.read_text(encoding='utf-8', errors='strict')
    # This module's comments are not nested. Scan proof text, not prose.
    code = re.sub(r'/\-.*?\-/', '', source, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',
                         re.sub(r'^#print axioms.*$', '', code, flags=re.M))
    names = re.findall(r'^theorem\s+(\w+)', source, re.M)
    assert len(names) == 5
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    declarations = []
    for name in names:
        qualified = 'JinWishart.' + name
        match = re.search(re.escape("'" + qualified + "' depends on axioms:") +
                          r'\s*\[([^\]]*)\]', diagnostic)
        assert match, qualified
        axioms = set(a.strip() for a in match[1].split(','))
        assert axioms <= allowed, qualified
        declarations.append(dict(name=qualified, axioms=sorted(axioms),
                                 author='Codex', independent_P4='PENDING'))

    # Bind the existing compiled project dependency closure actually selected
    # by LEAN_PATH, without describing its cached modules as recompiled here.
    closure, pending = {}, [MODULE]
    while pending:
        module = pending.pop()
        if module in closure:
            continue
        relative = Path(module.replace('.', '/'))
        lean = PROJECT / relative.with_suffix('.lean')
        olean = LIBRARY / relative.with_suffix('.olean')
        assert lean.exists() and olean.exists(), module
        content = lean.read_text(encoding='utf-8', errors='strict')
        closure[module] = dict(source=lean.relative_to(ROOT).as_posix(),
            source_sha256=digest(lean), compiled_sha256=digest(olean),
            check='NEW_LEAF_PASS' if module == MODULE else 'EXISTING_CACHED_DEPENDENCY')
        pending.extend(re.findall(r'^import\s+(JinWishartFormalization[.\w]*)',
                                  content, flags=re.M))
    compiled = LIBRARY / Path(MODULE.replace('.', '/') + '.olean')
    assert compiled.stat().st_mtime >= source_path.stat().st_mtime
    assert log.stat().st_mtime >= source_path.stat().st_mtime
    rejected = (HERE / 'local-energy-2.txt').read_text(encoding='utf-8')
    assert 'error:' in rejected and 'sorryAx' in rejected
    control = ROOT / 'verification/WISHART_RANDOM_SUBSPACE_CONTROL_20261016.json'
    numerical = json.loads(control.read_text(encoding='utf-8'))
    assert numerical['source_sha256'] == digest(ROOT / 'experiments/gaussian_random_subspace_control.py')
    result = dict(collected_utc=datetime.now(timezone.utc).isoformat(),
        module=MODULE, declarations=declarations, source_sha256=digest(source_path),
        log_sha256=digest(log), compiled_sha256=digest(compiled),
        project_dependency_closure=closure, toolchain=(PROJECT/'lean-toolchain').read_text().strip(),
        dependency_manifest_sha256=digest(PROJECT/'lake-manifest.json'),
        evidence={p.name:digest(p) for p in HERE.iterdir()
                  if p.is_file() and p.name != 'audit.json'},
        numeric_control=dict(path=control.relative_to(ROOT).as_posix(),sha256=digest(control)),
        local_model=dict(name='deepseek-prover-v2:7b', calls=2, accepted=0,
            outcomes=['REJECTED_PLACEHOLDER', 'LEAN_REJECTED_EXACT_SEARCH_FAILED'],
            scope='Short fixed-energy lemma, GUIDED_COLLABORATION; not P4'),
        validation_scope='Five new leaf declarations; no facade change or complete build',
        independent_review='PENDING; prior Step report does not cover this new module',
        publication='Existing paper and release archives unchanged',
        status='PASS kernel, standard-axiom, source-binding and numerical-control audits')
    (HERE/'audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(f'PASS {len(declarations)} audited declarations; {len(closure)} project dependencies bound.')


if __name__ == '__main__':
    main()
