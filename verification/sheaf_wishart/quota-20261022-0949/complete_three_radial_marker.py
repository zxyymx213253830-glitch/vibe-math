"""Point the still-unaccepted target at new immutable successful checker evidence."""
from pathlib import Path
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
tag='three-radial-v2-ThreeDimensionalRadialIntegral'
ap=run/('acceptance-'+tag+'.json');assert not ap.exists()
old=run/'three-radial-retired-marker/retired-acceptance-three-radial-ThreeDimensionalRadialIntegral.json'
ev=a.read(old);ev.update(target_lock=a.rel(run/('locks-'+tag+'.json')),check=a.rel(run/('check-'+tag+'.json')))
a.write(ap,ev)
sp=R/'verification/central_mixed_moments/spec.json';s=a.read(sp)
for t in s['targets']:
 if t['module']=='JinWishartFormalization.ThreeDimensionalRadialIntegral':
  assert t['count']==1;t['log']='verification/sheaf_wishart/'+tag+'-20261022-locked.txt'
a.write(sp,s)
release=run/'three-radial-release.json';c=a.read(release);assert c['name']=='three-radial'
(run/'three-radial-retired-marker/retired-three-radial-release.json').write_bytes(release.read_bytes())
c['name']='three-radial-v2';c['scope']+=' 初次验收因checker成功标签不符守卫拒绝，完整保留旧锁/日志/指针并退役旧节点；v2仅修输出标记，精确类型/证明/P4哈希未变，重新串行核验，守卫未改。'
a.write(release,c)
a.verify_acceptance(ev)
print('NEW_IMMUTABLE_TYPE_RECEIPT_VERIFIED; PROOF_AND_P4_UNCHANGED')
