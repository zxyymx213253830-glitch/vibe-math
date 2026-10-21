"""Check that locally committed proof bytes match the accepted source hashes."""
from pathlib import Path
import sys,subprocess,hashlib,json
R=Path(__file__).resolve().parents[3];run=Path(__file__).parent
sys.path.insert(0,str(R/'sheaf/wishart/tools'))
import sheaf as a
git=r'D:\MinGit\cmd\git.exe';audit=a.read(R/'verification/central_mixed_moments/audit.json')
names=['GramRankSpectralCoefficient','RectangularDeterminantExpansion','AveragedCauchyBinet','GramMinorCoefficientBound','GramMinorLogDomination','ActualSingularPositiveLog','ExpectedLogDetDerivative']
rows=[]
for name in names:
 mod='JinWishartFormalization.'+name;p=a.LEAN/'JinWishartFormalization'/(name+'.lean');rel=a.rel(p)
 data=subprocess.check_output([git,'show','HEAD:'+rel],cwd=R)
 stored=hashlib.sha256(data).hexdigest();current=a.sha(p);bound=audit['modules'][mod]['source_sha256']
 assert stored==current==bound,(rel,stored,current,bound)
 rows.append(dict(source=rel,committed_sha256=stored,working_sha256=current,audit_sha256=bound))
result=dict(status='PASS exact committed/working/audit source bytes',head=subprocess.check_output([git,'rev-parse','HEAD'],cwd=R,text=True).strip(),items=rows,scope='Archive integrity only; not another compiler run',collected_utc=a.now())
a.write(run/'git-source-byte-audit.json',result);print('SOURCE_BYTE_AUDIT_PASS',len(rows))
