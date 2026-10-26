"""Commit already accepted929 evidence; no repeat acceptance or Lean checks."""
from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
git='D:/MinGit/cmd/git.exe'
c=json.loads((run/'noncentral-spectral-orbit-release.json').read_text(encoding='utf-8'))
summary=json.loads((run/'noncentral-spectral-orbit-summary.json').read_text(encoding='utf-8'))
assert summary['items']==929 and summary['acceptance_records_current']==159
audit=json.loads((R/'verification/central_mixed_moments/audit.json').read_text(encoding='utf-8'))
assert audit['total_declarations']==929
for name in ['HermitianSpectralOrbit','ActualNoncentralSpectralOrbitLaw']:
    src='theory/jin_wishart_formalization/JinWishartFormalization/'+name+'.lean'
    lock=json.loads((run/('locks-noncentral-spectral-orbit-'+name+'.json')).read_text(encoding='utf-8'))
    assert hashlib.sha256((R/src).read_bytes()).hexdigest()==lock['definition_dependencies'][src]
out=subprocess.check_output([git,'status','--porcelain','-uall','-z'],cwd=R).decode('utf-8')
entries=[v for v in out.split('\0') if v]
assert not any('R' in v[:2] or 'C' in v[:2] for v in entries)
own=[v[3:] for v in entries if not v[3:].startswith(('.mimosa/','.workbuddy/','.write_probe.tmp','output/screenshots/','tmp/'))]
assert own
subprocess.run([git,'add','--']+own,cwd=R,check=True)
subprocess.run([git,'-c','core.whitespace=cr-at-eol','diff','--cached','--check'],cwd=R,check=True)
subprocess.run([git,'commit','-m',c['commit']],cwd=R,check=True)
for name in ['HermitianSpectralOrbit','ActualNoncentralSpectralOrbitLaw']:
    src='theory/jin_wishart_formalization/JinWishartFormalization/'+name+'.lean'
    assert subprocess.check_output([git,'show','HEAD:'+src],cwd=R)==(R/src).read_bytes()
print('COMMITTED_VERIFIED929_SOURCE_BYTES_MATCH; no push, no repeated acceptance')
