from pathlib import Path
from datetime import datetime, timezone
import sys
R = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(R / 'sheaf/wishart/tools'))
import sheaf as a
now = datetime.now(timezone.utc)
deadline = '2026-10-30T16:20:04+00:00'
assert now < datetime.fromisoformat(deadline)
for p in [a.SESSION/'STOP', a.SESSION/'compute.lock', a.SESSION/'runner.lock',
          a.SESSION/'CODEX_REVIEW', a.PROJECT/'coord/operation.lock', a.PROJECT/'coord/runner.lock']:
    assert not p.exists(), str(p)
cp = a.PROJECT/'coord/claims/quota-20261022-0949.lock'
sp = a.SESSION/'state.json'
c, s = a.read(cp), a.read(sp)
assert c['token'] == s['current_coordinator_token'] == 'd4b78a7c1a0449debe4e04635d41d232'
receipt = R/'verification/sheaf_wishart/quota-20261022-0949/resume-20261030-1420.json'
assert not receipt.exists()
old = {a.rel(p): a.sha(p) for p in [cp, sp]}
c.update(technical_lease_utc=deadline, renewed_utc=now.isoformat(), user_deadline_utc=deadline,
         authorization='User requested two hours of continued research', status='ACTIVE_TWO_HOURS', no_user_hard_deadline=False)
s.update(deadline_utc=deadline, user_deadline_utc=deadline, user_hard_deadline=True,
         deadline_is_technical_lease=False, resumed_utc=now.isoformat(), updated_utc=now.isoformat(),
         stage='ACTIVE_TWO_HOURS_20261030_1420', authorization='User requested two hours; autonomous Qoder/cloud collaboration permitted',
         current_quota_note='2026-10-30 14:20 UTC ordinaryUsageAllowed true, primary24 weekly46; no reset used')
a.write(cp,c); a.write(sp,s)
a.write(receipt,dict(resumed_utc=now.isoformat(), deadline_utc=deadline, old_hashes=old,
                     token=c['token'], idle_locks_checked=True, ordinaryUsageAllowed=True,
                     primary_used=24, weekly_used=46, no_purchase_or_reset=True))
print('RESUMED', deadline)
