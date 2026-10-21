from pathlib import Path
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
names=sys.argv[1:];tag='gram-minor' if len(names)==2 else names[0]
snap=run/(tag+'-snapshot');snap.mkdir(exist_ok=False)
intro='P4 adversarial review, <=500 words, problems only. No tools, no invented API checking, no independent compilation. All supplied new source proof bodies are Codex. Distinguish actual mathematical gaps from optional API questions. Exact pinned Lean checks already exit0/standard3axioms; these do not replace your logical review. No general probability offset or full subset Cauchy-Binet claim in these sources. All zero shapes included. Existing matrix_rank_compression is a checked deterministic finite-linear-algebra dependency.\n\n'
inputs={}
for name in names:
 p=a.LEAN/'JinWishartFormalization'/(name+'.lean');data=p.read_bytes();(snap/p.name).write_bytes(data)
 inputs[p.name]=dict(sha256=a.sha(p),supplied='Full source')
 intro+='\nSOURCE '+p.name+'\n'+data.decode('utf-8')
prompt=run/('p4-'+tag+'-prompt.txt');prompt.write_text(intro,encoding='utf-8')
a.write(run/(tag+'-review-request.json'),dict(inputs=inputs,prompt_sha256=a.sha(prompt)))
print(a.rel(prompt))
