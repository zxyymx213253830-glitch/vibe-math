"""One bounded read-only Claude Code review; preserve real raw events/receipt."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--prompt',required=True)
    parser.add_argument('--output-prefix',required=True)
    parser.add_argument('--seconds',type=int,default=120)
    args=parser.parse_args()
    prompt=Path(args.prompt).resolve(); prefix=Path(args.output_prefix).resolve()
    prefix.parent.mkdir(parents=True,exist_ok=True)
    cli=Path(r'D:\ClaudeCode\node_modules\@anthropic-ai\claude-code\bin\claude.exe')
    cmd=[str(cli),'-p',prompt.read_text(encoding='utf-8'),'--model','sonnet',
         '--tools','','--strict-mcp-config','--no-session-persistence',
         '--output-format','stream-json','--verbose','--max-budget-usd','0.50',
         '--permission-mode','dontAsk']
    assert len(subprocess.list2cmdline(cmd))<29000
    env=os.environ.copy();env.update(CI='true',NO_COLOR='1')
    started=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
    raw=Path(str(prefix)+'.raw.jsonl');stderr=Path(str(prefix)+'.stderr.txt')
    with raw.open('wb') as out,stderr.open('wb') as err:
        proc=subprocess.Popen(cmd,cwd=Path(__file__).resolve().parents[2],env=env,
                              stdin=subprocess.DEVNULL,stdout=out,stderr=err)
        try: code=proc.wait(timeout=args.seconds)
        except subprocess.TimeoutExpired:
            subprocess.run(['taskkill','/PID',str(proc.pid),'/T','/F'],
                           stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
            proc.wait();code=124
    events=[json.loads(line) for line in raw.read_text(encoding='utf-8').splitlines() if line.strip()]
    result=next((e for e in reversed(events) if e.get('type')=='result'),{})
    report=dict(started_utc=started,ended_utc=datetime.now(timezone.utc).isoformat(),
                seconds=time.monotonic()-tick,exit_code=code,requested_model='sonnet',
                prompt_sha256=hashlib.sha256(prompt.read_bytes()).hexdigest(),
                runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                tools_disabled=True,reported_models=sorted(result.get('modelUsage',{})),
                reported_total_cost_usd=result.get('total_cost_usd'),
                is_error=result.get('is_error',True),
                scope='Model feedback only; no independent compilation or human review')
    if code==0 and not result.get('is_error',True):
        Path(str(prefix)+'.response.md').write_text(result.get('result','')+'\n',encoding='utf-8')
    Path(str(prefix)+'.receipt.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report))
    raise SystemExit(code)


if __name__=='__main__': main()
