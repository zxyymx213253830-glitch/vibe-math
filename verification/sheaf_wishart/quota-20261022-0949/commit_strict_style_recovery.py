"""Preserve immutable verified bytes; recover only Git blank-at-EOF style failure."""
from pathlib import Path
import subprocess,hashlib,json
root=Path.cwd();run=root/'verification/sheaf_wishart/quota-20261022-0949';git='D:/MinGit/cmd/git.exe'
src='theory/jin_wishart_formalization/JinWishartFormalization/ActualCentralTwoByTwoStrictCrossing.lean'
lock=json.loads((run/'locks-actual-two-strict-ActualCentralTwoByTwoStrictCrossing.json').read_text())
assert hashlib.sha256((root/src).read_bytes()).hexdigest()==lock['definition_dependencies'][src]
style=subprocess.run([git,'-c','core.whitespace=cr-at-eol','diff','--cached','--check'],capture_output=True,text=True)
assert style.returncode==2 and style.stdout.strip()==src+':64: new blank line at EOF.' and not style.stderr
# Exact sole style complaint recorded above; do not mutate hashed accepted proof bytes.
subprocess.run([git,'commit','-m','Close actual central two by two strict T3 crossing probability'],check=True)
assert hashlib.sha256(subprocess.check_output([git,'show','HEAD:'+src])).hexdigest()==hashlib.sha256((root/src).read_bytes()).hexdigest()
print('COMMITTED_IMMUTABLE_BYTES_MATCH; blank-at-EOF only style waiver, no Lean/audit guard changed')
