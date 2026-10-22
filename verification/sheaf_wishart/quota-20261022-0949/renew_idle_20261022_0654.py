"""Renew only the same idle coordinator after a fresh allowed-quota observation."""
from pathlib import Path
import datetime,json
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
record=run/'idle-renewal-20261022-0654.json';assert not record.exists()
statepath=R/'.tools/central-mixed-moments-20261019/state.json'
claimpath=R/'sheaf/wishart/coord/claims/quota-20261022-0949.lock'
read=lambda p:json.loads(p.read_text(encoding='utf-8'))
for p in [R/'.tools/central-mixed-moments-20261019/compute.lock',R/'sheaf/wishart/coord/operation.lock']:assert not p.exists(),str(p)
state=read(statepath);claim=read(claimpath)
assert state['current_coordinator_token']==claim['token']=='d4b78a7c1a0449debe4e04635d41d232'
now=datetime.datetime.now(datetime.timezone.utc);deadline=(now+datetime.timedelta(hours=2)).isoformat()
obs=dict(observed_utc='2026-10-22T06:54:29+00:00',ordinaryUsageAllowed=True,primary_used_percent=1,weekly_used_percent=74,no_reset_credit_used=True,interruption_note='Prior observed primary100 still ordinarytrue at03:22; intervening exhaustion not asserted without evidence. Current window naturally differs; no coupon or purchase.')
record.write_text(json.dumps(dict(renewed_utc=now.isoformat(),old_claim=claim,old_state_deadline=state['deadline_utc'],new_technical_lease=deadline,observation=obs,idle_operation_and_compute_locks=True),ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
claim['technical_lease_utc']=deadline;claim['renewed_utc']=now.isoformat()
state.update(deadline_utc=deadline,updated_utc=now.isoformat(),current_quota_note='ordinaryUsageAllowed=true primary1% weekly74% observed06:54UTC; no reset credit used',deadline_is_technical_lease=True)
for p,d in [(claimpath,claim),(statepath,state)]:p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('IDLE_SAME_COORDINATOR_RENEWED',deadline)
