"""Save completed700 and the still-allowed rounded100 observation; no Lean."""
from pathlib import Path
import json,datetime
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
session=R/'.tools/central-mixed-moments-20261019';p=session/'state.json'
assert not (session/'compute.lock').exists() and not (R/'sheaf/wishart/coord/operation.lock').exists()
s=json.loads(p.read_text(encoding='utf-8'))
s['current_quota_note']='ordinaryUsageAllowed=true primary rounded100% weekly90% at2026-10-22 08:53:47UTC; no actual refusal observed, no reset credits used'
s['checkpoint']+=' Next canonical normal-form exact preflight11cases/55controls PASS, not proof/not counted700; source not started. See updated WISHART_NEXT_WIDE_POSITIVE_COORDINATE_CARD.md.'
s['updated_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
p.write_text(json.dumps(s,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
out=dict(utc=s['updated_utc'],items=700,acceptance_records_current=49,facade='facade-81',
 research_commit='d115000',next_preflight_commit='3e74106',ordinaryUsageAllowed=True,
 quota_observed_utc='2026-10-22T08:53:47Z',primary_rounded_used=100,weekly_used=90,
 no_exhaustion_claim=True,no_active_lean=True,next_source_started=False,
 next_card='notes/WISHART_NEXT_WIDE_POSITIVE_COORDINATE_CARD.md',
 human_review='REQUIRED',full_lake_build='NOT_RUN',linux_independent_kernel='NOT_RUN')
(run/'checkpoint-700-20261022.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('SAVED700; ROUNDED100_STILL_ALLOWED; AUTOMATION_CONTINUES')
