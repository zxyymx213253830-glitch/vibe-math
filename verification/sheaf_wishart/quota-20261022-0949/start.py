"""New user-authorized quota run, preserving the closed fixed-hour session."""
from pathlib import Path
from datetime import datetime, timezone, timedelta
import os, sys, uuid, json
R = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(R/'sheaf/wishart/tools'))
import sheaf as a
run = Path(__file__).parent
claim_path = a.PROJECT/'coord/claims/quota-20261022-0949.lock'
assert not (a.SESSION/'compute.lock').exists()
assert not (a.PROJECT/'coord/operation.lock').exists()
assert not list((a.PROJECT/'coord/claims').glob('*.lock'))
assert not (run/'claim.json').exists(), 'One-off start already recorded'
tick = datetime.now(timezone.utc)
claim = dict(token=uuid.uuid4().hex, started_utc=tick.isoformat(),
    technical_lease_utc=(tick+timedelta(hours=2)).isoformat(),
    authorization='User: continue useful research until current ordinary Codex quota is unavailable.',
    no_user_hard_deadline=True, single_coordinator=True)
fd = os.open(claim_path, os.O_CREAT|os.O_EXCL|os.O_WRONLY)
with os.fdopen(fd, 'w', encoding='utf-8') as f: json.dump(claim, f, indent=2)
a.write(run/'claim.json', claim)
state = a.read(a.SESSION/'state.json')
a.write(run/'prior-state.json', state)
for key in ['ended_utc','pause_reason']: state.pop(key, None)
state.update(stage='ACTIVE_WISHART_QUOTA_20261022', authorization=claim['authorization'],
    deadline_utc=claim['technical_lease_utc'], deadline_is_technical_lease=True,
    current_coordinator_token=claim['token'], resumed_utc=tick.isoformat(),
    updated_utc=tick.isoformat(), automation_status='PAUSED',
    current_quota_note='ordinaryUsageAllowed=true; primary0%, weekly59%, checked2026-10-22 01:49UTC. No purchases/resets/account switches.')
a.write(a.SESSION/'state.json',state)
a.ledger('New quota authorization; old fixed hour remains CLOSED. Baseline610/auditPASS/facade64; next exact subset Cauchy-Binet.')
print(json.dumps(claim))
