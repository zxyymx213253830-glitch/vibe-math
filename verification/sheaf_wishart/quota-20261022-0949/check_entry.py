"""Only entry to the shared serial Lean gate for this quota run."""
from pathlib import Path
from datetime import datetime,timezone
import sys,json
R=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
module,tag=sys.argv[1:3]
source=(R/sys.argv[3]).resolve() if len(sys.argv)>3 else a.LEAN/Path(module.replace('.','/')+'.lean')
state=a.read(a.SESSION/'state.json')
claim=a.read(a.PROJECT/'coord/claims/quota-20261022-0949.lock')
assert state['current_coordinator_token']==claim['token']
assert datetime.now(timezone.utc)<datetime.fromisoformat(claim['technical_lease_utc'])
with a.exclusive(a.PROJECT/'coord/operation.lock','codex-quota-20261022-0949'):
 result=a.gated(source,module,tag,source.parent if len(sys.argv)>3 else None)
 if module=='JinWishartFormalization':
  result['gated_helper_exit_code']=result['exit_code']
  a.write(R/'verification/sheaf_wishart'/(tag+'.receipt.json'),result)
 print(json.dumps(result))
sys.exit(result['exit_code'])
