import fcntl,tempfile,subprocess,sys,json,pathlib,shutil
results={"python":sys.version,"bash":shutil.which("bash"),"tmux":shutil.which("tmux")}
with tempfile.TemporaryDirectory(prefix="sheaf-platform-smoke-") as directory:
 lock=pathlib.Path(directory)/"compute.lock"
 child="import fcntl,sys;f=open(sys.argv[1],'a');\ntry:fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)\nexcept BlockingIOError:sys.exit(73)"
 with lock.open("a") as held:
  fcntl.flock(held,fcntl.LOCK_EX|fcntl.LOCK_NB)
  blocked=subprocess.run([sys.executable,"-c",child,str(lock)],capture_output=True,timeout=10)
  assert blocked.returncode==73,(blocked.returncode,blocked.stderr)
  fcntl.flock(held,fcntl.LOCK_UN)
 acquired=subprocess.run([sys.executable,"-c",child,str(lock)],capture_output=True,timeout=10)
 assert acquired.returncode==0,(acquired.returncode,acquired.stderr)
 results["fcntl_cross_process_exclusion"]="PASS"
 results["fcntl_release_control"]="PASS"
 sock=str(pathlib.Path(directory)/"private-tmux.sock")
 try:
  p=subprocess.run(["tmux","-S",sock,"new-session","-d","-s","probe","sleep 20"],capture_output=True,timeout=10)
  assert p.returncode==0,p.stderr
  q=subprocess.run(["tmux","-S",sock,"has-session","-t","probe"],capture_output=True,timeout=10)
  assert q.returncode==0,q.stderr
  results["tmux_private_session"]="PASS"
 finally:
  subprocess.run(["tmux","-S",sock,"kill-server"],capture_output=True,timeout=10)
 results["owned_tmux_cleanup"]="DONE"
print(json.dumps(results))
