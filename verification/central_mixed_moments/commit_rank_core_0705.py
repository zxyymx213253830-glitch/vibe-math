"""Stage exact owned core milestone files, leaving other drafts untouched."""
from pathlib import Path
import subprocess
root=Path(__file__).resolve().parents[2]
base=root/'verification/central_mixed_moments'
names=['CorrelatedRankUpperBound','CorrelatedRankWitness','MatrixRankCompression',
       'CorrelatedGaussianGenericRank','CorrelatedLogDetGenericRank','CorrelatedMinimumZeroAtom']
files=[root/'theory/jin_wishart_formalization/JinWishartFormalization.lean',
 root/'notes/WISHART_GENERIC_RANK.md',root/'notes/WISHART_STATUS.md',
 root/'experiments/correlated_rank_compression_control.py',base/'correlated-rank-compression-control.json',
 root/'experiments/correlated_rank_zero_mode_control.py',base/'correlated-rank-zero-mode-control.json',
 base/'spec.json',base/'audit.json',base/'prepare_rank_review_0705.py',base/'register_rank_0705.py',base/'register_zero_atom_0705.py',
 Path(__file__).resolve()]
files += [root/'theory/jin_wishart_formalization/JinWishartFormalization'/(name+'.lean') for name in names]
for prefix in ['p1-correlated-rank-upper-0705','p4-rank-algebra-0705','p4-rank-compression-0705',
 'p4-gaussian-rank-0705','p4-logdet-generic-rank-0705','p4-minimum-zero-atom-0705','rank-upper-0705-',
 'rank-witness-0705-','rank-compression-0705-','gaussian-generic-rank-0705-',
 'logdet-generic-rank-0705-','minimum-zero-atom-0705-','facade-46']:
    files.extend(p for p in base.glob(prefix+'*') if p.is_file())
for tag in ['rank-algebra-0705','rank-compression-0705','gaussian-rank-0705','logdet-generic-rank-0705','minimum-zero-atom-0705']:
    files.append(base/(tag+'-review-request.json'))
    files.extend((base/(tag+'-snapshot')).glob('*.lean'))
files=sorted(set(files))
assert all(p.exists() for p in files)
git=r'D:\MinGit\cmd\git.exe'
subprocess.run([git,'add','--']+[str(p.relative_to(root)) for p in files],cwd=root,check=True)
subprocess.run([git,'diff','--cached','--stat'],cwd=root,check=True)
subprocess.run([git,'commit','-m','Prove generic rank and explicit correlated logdet prelog'],cwd=root,check=True)
