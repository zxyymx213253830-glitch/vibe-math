from pathlib import Path
import subprocess,json,time,shlex
ROOT=Path(r"D:\vibe math")
OUT=ROOT/"verification/sheaf_platform_benchmark"
BASE=["wsl.exe","--distribution","SheafBenchUbuntu","--user","root","--exec"]
def call(name,args,timeout=180):
    target=OUT/(name+".receipt.json")
    if target.exists(): raise RuntimeError("Existing receipt: "+str(target))
    start=time.monotonic()
    p=subprocess.run(BASE+args,capture_output=True,timeout=timeout)
    # Native Linux command outputs UTF8, WSL errors can be UTF16LE.
    def decode(b): return b.decode("utf-16-le" if b"\x00" in b else "utf8",errors="replace")
    data=dict(command=BASE+args,exit_code=p.returncode,wall_seconds=time.monotonic()-start,stdout=decode(p.stdout),stderr=decode(p.stderr))
    target.write_text(json.dumps(data,indent=2,ensure_ascii=False)+"\n",encoding="utf8")
    print(name,p.returncode,data["stdout"][:2000],data["stderr"][:1000],flush=True)
    if p.returncode: raise RuntimeError(name+" failed")
    return data
meta=call("linux-preflight-20261021",["sh","-c","uname -a; cat /etc/os-release; command -v python3; command -v tmux || true"])
setup=call("linux-copy-20261021",["python3","-c",r"""import pathlib,shutil,json,time
base=pathlib.Path('/root/sheaf-platform-benchmark-20261021')
base.mkdir(exist_ok=False)
source=pathlib.Path('/mnt/d/vibe math')
t=time.monotonic()
shutil.copytree(source/'.tools/sheaf-platform-benchmark-20261021/snapshot',base/'snapshot',ignore=shutil.ignore_patterns('__pycache__'))
shutil.copyfile(source/'experiments/sheaf_platform_benchmark.py',base/'sheaf_platform_benchmark.py')
print(json.dumps({'copy_seconds':time.monotonic()-t,'linux_directory':str(base)}))
"""])
script="/root/sheaf-platform-benchmark-20261021/sheaf_platform_benchmark.py"
call("linux-home-run-20261021",["python3","-X","utf8",script,"run","--snapshot","/root/sheaf-platform-benchmark-20261021/snapshot","--output","/mnt/d/vibe math/verification/sheaf_platform_benchmark/linux-home-20261021.json"])
call("linux-mounted-run-20261021",["python3","-X","utf8",script,"run","--snapshot","/mnt/d/vibe math/.tools/sheaf-platform-benchmark-20261021/snapshot","--output","/mnt/d/vibe math/verification/sheaf_platform_benchmark/linux-mounted-20261021.json"])
