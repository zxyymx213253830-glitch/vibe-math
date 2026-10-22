"""One-off metadata repair: never count a private helper as a public target.

No proof/checker/review/olean/Lean log changes and no repeated Lean execution.
Retain failed manifests and retire duplicate live ownership before replacement.
"""
from pathlib import Path
import json, re, hashlib, sys
R=Path(__file__).resolve().parents[3]; run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
assert not (a.SESSION/'compute.lock').exists()
assert not (a.PROJECT/'coord/operation.lock').exists()
record=run/'canonical-export-repair.json'; assert not record.exists()
archive=run/'canonical-block-retired-export-manifests'; archive.mkdir(exist_ok=False)
oldcards=a.read(run/'cards-canonical-block.json'); newcards=[]; previous=None
files={}; proof_hashes={}
def retain(p):
    dest=archive/p.name; assert not dest.exists()
    raw=p.read_bytes(); dest.write_bytes(raw); files[a.rel(p)]=hashlib.sha256(raw).hexdigest()
for card in oldcards:
    for ident,decl,deps in card['nodes']:
        p=a.PROJECT/'dag/nodes'/(ident+'.json'); retain(p); node=a.read(p)
        node['superseded_declaration']=node.pop('declaration')
        node['superseded_module']=node.pop('module'); node['target']=False
        node['verification']=dict(status='superseded_export_manifest_error',
          reason='Private helper mistakenly exported by parser; no proof/source/type check failed. Eight public exports relocked in v2; all old manifests retained.')
        a.write(p,node)
for ci,card in enumerate(oldcards):
    oldtag=card['tag']; tag=oldtag.replace('canonical-block-','canonical-block-v2-',1)
    lp=run/('locks-'+oldtag+'.json'); lock=a.read(lp)
    src=R/lock['source']; proof_hashes[a.rel(src)]=a.sha(src)
    body=src.read_text(encoding='utf-8')
    public=['JinWishart.'+n for n in re.findall(r'^theorem\s+(\w+)',body,re.M)]
    printed=re.findall(r'^#print axioms (\S+)',body,re.M)
    assert public==printed
    removed=set(lock['statements'])-set(public)
    assert removed==({'JinWishart.realRoot'} if ci==0 else set())
    lock['statements']={n:lock['statements'][n] for n in public}
    newlp=run/('locks-'+tag+'.json'); assert not newlp.exists(); a.write(newlp,lock)
    a.validate_locks(a.rel(newlp))
    oldcheck=a.read(run/('check-'+oldtag+'.json'))
    assert oldcheck['success'] and oldcheck['source_sha256']==a.sha(src)
    check=dict(oldcheck,target_lock_sha256=a.sha(newlp),
      export_manifest_repair='Source and eight literal types unchanged; reuse the exact successful final kernel/type receipts, not a new execution.')
    a.write(run/('check-'+tag+'.json'),check)
    nodes=[]
    for index,decl in enumerate(public):
        ident='L-canonical-block-v2-'+decl.split('.')[-1]; ds=[previous] if previous else []
        target=ci==len(oldcards)-1 and index==len(public)-1
        a.write(a.PROJECT/'dag/nodes'/(ident+'.json'),dict(id=ident,kind='lemma',target=target,
          module=lock['module'],declaration=decl,stmt_deps=[],proof_deps=ds,
          proof=[dict(text='Exact unchanged source; independent eight public type checks and scoped P4 unchanged. Private helper remains checked transitively, not a public target.',uses=ds)],
          verification=dict(status='checked_pending_review')))
        nodes.append([ident,decl.split('.')[-1],ds]); previous=ident
    newcards.append(dict(tag=tag,module=card['module'],nodes=nodes))
    ap=run/('acceptance-'+oldtag+'.json'); retain(ap); ev=a.read(ap)
    ev['target_lock']=a.rel(newlp); ev['check']=a.rel(run/('check-'+tag+'.json'))
    a.write(run/('acceptance-'+tag+'.json'),ev)
    # Remove only our unaccepted old acceptance pointer after preserving bytes.
    assert ap.resolve().parent==run.resolve() and ap.name.startswith('acceptance-canonical-block-')
    ap.unlink()
a.write(run/'cards-canonical-block-v2.json',newcards)
sp=R/'verification/central_mixed_moments/spec.json'; retain(sp); spec=a.read(sp)
for target in spec['targets']:
    if target['module']=='JinWishartFormalization.CanonicalBlockSpectrum':
        assert target['count']==6; target['count']=5
assert sum(len(c['nodes']) for c in newcards)==8
a.write(sp,spec)
release=run/'canonical-block-release.json'; retain(release); c=a.read(release)
assert c['name']=='canonical-block' and c['new_count']==8 and c['total']==688
c['name']='canonical-block-v2'; a.write(release,c)
a.write(record,dict(repaired_utc=a.now(),retained_files=files,unchanged_proof_hashes=proof_hashes,
 retired_nodes=9,public_targets=8,private_helper='realRoot',
 cause='Target parser includes private theorem command but auditor correctly counts public theorem declarations only.',
 audit_failure='Initial audit refused count6 against five public CanonicalBlockSpectrum declarations; no failed audit accepted.',
 kernel_and_type_receipts_reused_unchanged=True,review_source_unchanged=True,
 audit_implementation_unchanged=True,source_final_reviewed=True))
print('REPAIRED_PUBLIC_EXPORTS8; RETIRED9_UNACCEPTED_NODES; PROOF/P4/CHECKER/COMPILER_RECEIPTS_UNCHANGED')
