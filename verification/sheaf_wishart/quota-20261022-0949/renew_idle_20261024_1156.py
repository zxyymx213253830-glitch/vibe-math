"""Renew same coordinator only after current allowed quota and idle checks."""
from pathlib import Path
from datetime import datetime,timedelta,timezone
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
receipt=run/'idle-renewal-20261024-1156.json';assert not receipt.exists()
for p in [a.SESSION/'compute.lock',a.SESSION/'runner.lock',a.SESSION/'CODEX_REVIEW',a.PROJECT/'coord/operation.lock',a.PROJECT/'coord/runner.lock']:
 assert not p.exists(),str(p)
cp=a.PROJECT/'coord/claims/quota-20261022-0949.lock';sp=a.SESSION/'state.json'
c=a.read(cp);s=a.read(sp);assert c['token']==s['current_coordinator_token']=='d4b78a7c1a0449debe4e04635d41d232'
now=datetime.now(timezone.utc);lease=(now+timedelta(hours=2)).isoformat()
old={a.rel(p):a.sha(p) for p in [cp,sp]}
c.update(technical_lease_utc=lease,renewed_utc=now.isoformat());a.write(cp,c)
s.update(deadline_utc=lease,updated_utc=now.isoformat(),current_quota_note='2026-10-24 11:55:51UTC ordinarytrue primary1 weekly16; two reset credits still available, never used. No interval activity/refusal observed or inferred.',stage='ACTIVE_WISHART_QUOTA_20261024');a.write(sp,s)
a.write(receipt,dict(renewed_utc=now.isoformat(),old_hashes=old,token=c['token'],technical_lease_utc=lease,idle_locks_checked=True,ordinaryUsageAllowed=True,quota_observed_utc='2026-10-24T11:55:51+00:00',primary_used=1,weekly_used=16,no_user_deadline=True,no_purchase_or_reset=True))
print('IDLE_ALLOWED_SAME_TOKEN_RENEWED',lease)
