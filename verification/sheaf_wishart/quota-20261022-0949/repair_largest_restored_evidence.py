"""Bind a fresh check after byte-exact restoration; retain original evidence."""
from pathlib import Path
import sys
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
lock=run/'locks-psi-candidate-largest-PsiCandidateLargestCDF.json'
a.validate_locks(a.rel(lock))
check=run/'check-psi-candidate-largest-PsiCandidateLargestCDF.json'
new=R/'verification/sheaf_wishart/psi-candidate-largest-restored-locked-recheck.receipt.json'
d=a.read(check); leaf=a.read(new)
assert leaf['success'] and leaf['source_sha256']==d['source_sha256']
assert leaf['source_sha256_before']==d['source_sha256']
backup=run/'psi-candidate-largest-original-check-before-restore.json'
assert not backup.exists()
a.write(backup,d)
d['leaf']=leaf;d['restored_byte_identical_fresh_check']=True;a.write(check,d)
specpath=R/'verification/central_mixed_moments/spec.json';spec=a.read(specpath)
matches=[x for x in spec['targets'] if x['module']=='JinWishartFormalization.PsiCandidateLargestCDF']
assert len(matches)==1
assert matches[0]['log']=='verification/sheaf_wishart/psi-candidate-largest-PsiCandidateLargestCDF-20261022-locked.txt'
matches[0]['log']=leaf['log'];a.write(specpath,spec)
print('RESTORED_SOURCE_CHECK_REBOUND; ORIGINAL CHECK RETAINED')
