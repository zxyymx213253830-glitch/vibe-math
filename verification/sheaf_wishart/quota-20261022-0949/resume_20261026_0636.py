"""Human-authorized resume, idle same-token lease and accepted commit recovery."""
from pathlib import Path
from datetime import datetime,timedelta,timezone
import json,subprocess,hashlib,sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
receipt=run/'idle-renewal-20261026-0636.json'
assert not receipt.exists()
for p in [a.SESSION/'compute.lock',a.SESSION/'runner.lock',a.SESSION/'CODEX_REVIEW',a.PROJECT/'coord/operation.lock',a.PROJECT/'coord/runner.lock']:
    assert not p.exists(),str(p)
cp=a.PROJECT/'coord/claims/quota-20261022-0949.lock';sp=a.SESSION/'state.json'
c=a.read(cp);s=a.read(sp)
assert c['token']==s['current_coordinator_token']=='d4b78a7c1a0449debe4e04635d41d232'
now=datetime.now(timezone.utc);lease=(now+timedelta(hours=2)).isoformat()
old={a.rel(p):a.sha(p) for p in [cp,sp]}
c.update(technical_lease_utc=lease,renewed_utc=now.isoformat());a.write(cp,c)
s.update(authorization='User explicitly resumed: 继续 on 2026-10-26; continue useful research until current ordinary quota unavailable.',resumed_utc=now.isoformat(),deadline_utc=lease,updated_utc=now.isoformat(),current_quota_note='2026-10-26 06:36:33UTC ordinarytrue primary1 weekly0; two reset credits available, never used; no gap activity inferred.',stage='ACTIVE_WISHART_QUOTA_20261026',automation_status='ACTIVE')
s.pop('pause_reason',None);a.write(sp,s)
a.write(receipt,dict(renewed_utc=now.isoformat(),old_hashes=old,token=c['token'],technical_lease_utc=lease,idle_locks_checked=True,ordinaryUsageAllowed=True,quota_observed_utc='2026-10-26T06:36:33+00:00',primary_used=1,weekly_used=0,no_user_deadline=True,no_purchase_or_reset=True))
print('IDLE_ALLOWED_SAME_TOKEN_RESUMED',lease)
