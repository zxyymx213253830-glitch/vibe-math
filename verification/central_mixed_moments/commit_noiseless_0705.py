"""Commit exact owned checked floor/moment milestone and its evidence."""
from pathlib import Path
import subprocess
root=Path(__file__).resolve().parents[2]
base=root/'verification/central_mixed_moments'
files=[root/'theory/jin_wishart_formalization/JinWishartFormalization.lean',
 root/'theory/jin_wishart_formalization/JinWishartFormalization/CorrelatedNoiselessSpectralFloor.lean',
 root/'theory/jin_wishart_formalization/JinWishartFormalization/CorrelatedNoiselessInverseMoments.lean',
 root/'notes/WISHART_NOISELESS_SPECTRAL_FLOOR.md',root/'notes/WISHART_NEXT_NOISELESS_OFFSET_CARD.md',
 root/'notes/WISHART_STATUS.md',base/'spec.json',base/'audit.json',
 root/'experiments/correlated_noiseless_floor_control.py',root/'experiments/noiseless_row_logdet_offset_preflight.py',
 base/'correlated-noiseless-floor-control.json',base/'noiseless-row-offset-preflight.json',
 base/'register_noiseless_0705.py',base/'check_facade_0705_receipt.py',Path(__file__).resolve()]
for prefix in ['noiseless-floor-0705-','noiseless-inverse-0705-',
               'p4-noiseless-floor-inverse-0705','facade-47','facade-48']:
    files.extend(p for p in base.glob(prefix+'*') if p.is_file())
tag='noiseless-floor-inverse-0705'
files.append(base/(tag+'-review-request.json'))
files.extend((base/(tag+'-snapshot')).glob('*.lean'))
assert all(p.exists() for p in files)
git=r'D:\MinGit\cmd\git.exe'
subprocess.run([git,'add','--']+[str(p.relative_to(root)) for p in sorted(set(files))],cwd=root,check=True)
subprocess.run([git,'commit','-m','Prove noiseless row spectral floor and every real inverse order'],cwd=root,check=True)
