from pathlib import Path
from datetime import datetime,timezone
import sys,json
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'sheaf/wishart/tools'))
import sheaf as a
module,tag=sys.argv[1:3]
source=(ROOT/sys.argv[3]).resolve() if len(sys.argv)>3 else ROOT/'theory/jin_wishart_formalization'/Path(module.replace('.','/')+'.lean')
state=a.read(a.SESSION/'state.json');claim=a.read(ROOT/'sheaf/wishart/coord/claims/gaussian-log-hour-20261021.lock')
assert state['current_coordinator_token']==claim['token']
assert datetime.now(timezone.utc)<datetime.fromisoformat(claim['hard_deadline_utc'])
with a.exclusive(a.PROJECT/'coord/operation.lock','codex-hour-20261021-1201'):
 result=a.gated(source,module,tag,source.parent if len(sys.argv)>3 else None)
 if module=='JinWishartFormalization':
  result['gated_helper_exit_code']=result['exit_code'];a.write(ROOT/'verification/sheaf_wishart'/(tag+'.receipt.json'),result)
 print(json.dumps(result))
sys.exit(result['exit_code'])
