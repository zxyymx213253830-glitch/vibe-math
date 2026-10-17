"""One bounded Qoder request, with tools disabled and byte-exact evidence."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--prompt', required=True)
    parser.add_argument('--output-prefix', required=True)
    parser.add_argument('--seconds', type=int, default=120)
    parser.add_argument('--model', default='Qwen3.8-Max')
    args = parser.parse_args()
    source = Path(args.prompt).resolve()
    prefix = Path(args.output_prefix).resolve()
    prefix.parent.mkdir(parents=True, exist_ok=True)
    prompt = source.read_text(encoding='utf-8')
    cmd = [r'C:\Program Files\nodejs\node.exe',
        r'D:\QoderCLI\node_modules\@qoder-ai\qodercli\bundle\qodercli.js',
        '--model', args.model, '--tools', '', '--strict-mcp-config',
        '--setting-sources', 'user', '--permission-mode', 'dont_ask',
        '--no-session-persistence', '--max-model-request-retries', '0',
        '--thinking', 'disabled', '--max-output-tokens', '4096',
        '--output-format', 'json', '-p', prompt]
    assert len(subprocess.list2cmdline(cmd)) < 29000, 'Shorten supplied context; no silent truncation'
    env = os.environ.copy()
    env.update(CI='true', NO_COLOR='1')
    started = datetime.now(timezone.utc).isoformat()
    tick = time.monotonic()
    with Path(str(prefix)+'.raw.json').open('wb') as out, \
         Path(str(prefix)+'.stderr.txt').open('wb') as err:
        proc = subprocess.Popen(cmd, cwd=Path(__file__).resolve().parents[2], env=env,
            stdin=subprocess.DEVNULL, stdout=out, stderr=err)
        try:
            code = proc.wait(timeout=args.seconds)
        except subprocess.TimeoutExpired:
            subprocess.run(['taskkill', '/PID', str(proc.pid), '/T', '/F'],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            proc.wait()
            code = 124
    report = dict(started_utc=started, ended_utc=datetime.now(timezone.utc).isoformat(),
        seconds=time.monotonic()-tick, exit_code=code, requested_model=args.model,
        tools_disabled=True, thinking='disabled', prompt_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        policy='One call; no retries; tools/MCP disabled; no independent compilation')
    if code == 0:
        raw = json.loads(Path(str(prefix)+'.raw.json').read_text(encoding='utf-8'))
        if not raw.get('is_error', True):
            Path(str(prefix)+'.response.md').write_text(raw['result']+'\n', encoding='utf-8')
            report['reported_model_usage'] = raw.get('modelUsage')
            report['reported_credits'] = raw.get('total_credits')
    Path(str(prefix)+'.receipt.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k:v for k,v in report.items() if k != 'reported_model_usage'}))
    raise SystemExit(code)


if __name__ == '__main__':
    main()
