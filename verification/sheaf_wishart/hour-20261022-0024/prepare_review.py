from pathlib import Path
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
names=sys.argv[1:]
tag=names.pop(0).split('=',1)[1] if names[0].startswith('--tag=') else ('gram-minor' if len(names)==2 else names[0])
snap=run/(tag+'-snapshot');snap.mkdir(exist_ok=False)
intro='P4 adversarial review, <=500 words, problems only. No tools, no invented API checking, no independent compilation. All supplied source proof bodies are Codex. Distinguish actual mathematical gaps from optional API questions. Exact pinned Lean checks already exit0/standard3axioms; these do not replace your logical review. Review ONLY the exact claims and explicit assumptions in the attached sources; do not assume positivity of dimensions, fullrank, finite measure, parameter uniformity or additional probability claims unless actually stated. A stochastic statement carries its own explicit measure/model conditions. Treat imported results as separately checked dependencies and ask for an exact signature only when a concrete semantic mismatch matters.\n\n'
inputs={}
for name in names:
 p=a.LEAN/'JinWishartFormalization'/(name+'.lean');data=p.read_bytes();(snap/p.name).write_bytes(data)
 inputs[p.name]=dict(sha256=a.sha(p),supplied='Full source')
 intro+='\nSOURCE '+p.name+'\n'+data.decode('utf-8')
prompt=run/('p4-'+tag+'-prompt.txt');prompt.write_text(intro,encoding='utf-8')
a.write(run/(tag+'-review-request.json'),dict(inputs=inputs,prompt_sha256=a.sha(prompt)))
print(a.rel(prompt))
