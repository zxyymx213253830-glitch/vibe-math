"""Retire unaccepted evidence; preserve exact type/proof while correcting success marker."""
from pathlib import Path
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
assert not (a.SESSION/'compute.lock').exists()
assert not (a.PROJECT/'coord/operation.lock').exists()
archive=run/'three-radial-retired-marker';archive.mkdir(exist_ok=False)
old='three-radial-ThreeDimensionalRadialIntegral'
ap=run/('acceptance-'+old+'.json')
raw=ap.read_bytes();(archive/('retired-'+ap.name)).write_bytes(raw);ap.unlink()
p=a.PROJECT/'dag/nodes/L-three-radial-lintegral_norm_volume_fin_three.json'
(archive/('retired-'+p.name)).write_bytes(p.read_bytes());n=a.read(p)
n['superseded_declaration']=n.pop('declaration');n['superseded_module']=n.pop('module')
n['target']=False;n['verification']=dict(status='superseded_checker_marker_error',reason='Independent literal type checked, but its success marker did not satisfy acceptance guard. Corrected marker only, new checker/new lock/new receipt; no guard change.')
a.write(p,n)
src=run/'SheafThreeRadialTargets.lean';dst=run/'SheafThreeRadialTargetsV2.lean'
assert not dst.exists()
body=src.read_text(encoding='utf-8')
assert body.count('logInfo "THREE_RADIAL_LITERAL_TYPE_PASS"')==1
dst.write_text(body.replace('logInfo "THREE_RADIAL_LITERAL_TYPE_PASS"','IO.println "SHEAF_TARGET_TYPES_EQ PASS"'),encoding='utf-8')
a.write(archive/'repair-record.json',dict(utc=a.now(),proof_sha256=a.sha(a.LEAN/'JinWishartFormalization/ThreeDimensionalRadialIntegral.lean'),old_checker_sha256=a.sha(src),new_checker_sha256=a.sha(dst),only_change='Success output marker; literal target/inferType/whnf/isDefEq unchanged',old_acceptance_sha256=__import__('hashlib').sha256(raw).hexdigest(),acceptance_guard_changed=False))
print('RETIRED_UNACCEPTED_MARKER_RECORD; NEW_CHECKER_READY')
