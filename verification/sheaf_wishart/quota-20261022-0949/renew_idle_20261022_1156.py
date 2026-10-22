"""Same-owner renewal after an interruption; no claim of work during the gap."""
from pathlib import Path
from datetime import datetime,timezone,timedelta
import json,hashlib
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
session=R/'.tools/central-mixed-moments-20261019';claim=R/'sheaf/wishart/coord/claims/quota-20261022-0949.lock'
state=session/'state.json';record=run/'idle-renewal-20261022-1156.json';assert not record.exists()
for p in [session/'compute.lock',session/'runner.lock',session/'CODEX_REVIEW',R/'sheaf/wishart/coord/operation.lock']:assert not p.exists(),str(p)
c=json.loads(claim.read_text(encoding='utf-8'));s=json.loads(state.read_text(encoding='utf-8'))
assert c['token']==s['current_coordinator_token']=='d4b78a7c1a0449debe4e04635d41d232'
now=datetime.now(timezone.utc);observed=datetime(2026,10,22,11,56,34,tzinfo=timezone.utc)
assert 0<=(now-observed).total_seconds()<240
before={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [claim,state]}
deadline=now+timedelta(hours=2);c.update(technical_lease_utc=deadline.isoformat(),renewed_utc=now.isoformat())
s.update(deadline_utc=deadline.isoformat(),updated_utc=now.isoformat(),current_quota_note='ordinaryUsageAllowed=true primary1% weekly90% at2026-10-22 11:56:34UTC; no reset credits used; no actual refusal observed during interruption')
for p,d in [(claim,c),(state,s)]:p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
record.write_text(json.dumps(dict(renewed_utc=now.isoformat(),old_hashes=before,token=c['token'],technical_lease_utc=deadline.isoformat(),idle_locks_checked=True,ordinaryUsageAllowed=True,quota_observed_utc=observed.isoformat(),primary_used=1,weekly_used=90,no_user_deadline=True,no_purchase_or_reset=True,no_interval_activity_claim=True),indent=2)+'\n',encoding='utf-8')
print(deadline.isoformat())
