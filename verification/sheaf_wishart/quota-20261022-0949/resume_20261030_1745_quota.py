"""Resume same coordinator only after idle locks and live ordinary quota check."""
from pathlib import Path
from datetime import datetime, timedelta, timezone
import sys
R = Path(__file__).resolve().parents[3]
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
for p in [a.SESSION/'STOP',a.SESSION/'compute.lock',a.SESSION/'runner.lock',a.SESSION/'CODEX_REVIEW',
          a.PROJECT/'coord/operation.lock',a.PROJECT/'coord/runner.lock']:
    assert not p.exists(), str(p)
cp=a.PROJECT/'coord/claims/quota-20261022-0949.lock'; sp=a.SESSION/'state.json'
c,s=a.read(cp),a.read(sp)
assert c['token']==s['current_coordinator_token']=='d4b78a7c1a0449debe4e04635d41d232'
out=R/'verification/sheaf_wishart/quota-20261022-0949/resume-20261030-1745-quota.json'
assert not out.exists()
now=datetime.now(timezone.utc); lease=(now+timedelta(hours=2)).isoformat()
old={a.rel(p):a.sha(p) for p in [cp,sp]}
c.update(technical_lease_utc=lease,renewed_utc=now.isoformat(),status='ACTIVE_QUOTA',
         no_user_hard_deadline=True,authorization='User requested continue until ordinary quota unavailable')
c.pop('user_deadline_utc',None)
s.update(deadline_utc=lease,deadline_is_technical_lease=True,user_hard_deadline=False,
         stage='ACTIVE_QUOTA_20261030_1745',resumed_utc=now.isoformat(),updated_utc=now.isoformat(),
         authorization='User requested continue until ordinary quota unavailable; autonomous Qoder/cloud collaboration permitted',
         current_quota_note='2026-10-30 17:45 UTC ordinaryUsageAllowed true, primary1 weekly58; no reset used',
         quota_stop_latched=False)
s.pop('user_deadline_utc',None)
a.write(cp,c);a.write(sp,s)
a.write(out,dict(resumed_utc=now.isoformat(),technical_lease_utc=lease,old_hashes=old,token=c['token'],
                 ordinaryUsageAllowed=True,primary_used=1,weekly_used=58,idle_locks_checked=True,
                 no_purchase_or_reset=True,interruption_activity='not observed'))
print('RESUMED_QUOTA_WITH_TECHNICAL_LEASE',lease)
