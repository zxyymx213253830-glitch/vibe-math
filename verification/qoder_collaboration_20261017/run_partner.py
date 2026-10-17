"""Bounded, tools-disabled Qoder collaboration with preserved raw responses."""
from datetime import datetime, timezone
import argparse
import json
import os
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('name')
    parser.add_argument('--seconds', type=int, default=150)
    parser.add_argument('--thinking', choices=['disabled', 'auto'], default='auto')
    args = parser.parse_args()
    prompt_file = HERE / (args.name + '-prompt.txt')
    prompt = prompt_file.read_text(encoding='utf-8')
    command = [r'C:\Program Files\nodejs\node.exe',
               r'D:\QoderCLI\node_modules\@qoder-ai\qodercli\bundle\qodercli.js',
               '--model', 'Qwen3.8-Max', '--tools', '', '--strict-mcp-config',
               '--setting-sources', 'user', '--permission-mode', 'dont_ask',
               '--no-session-persistence', '--max-model-request-retries', '0',
               '--thinking', args.thinking, '--max-output-tokens', '4096',
               '--output-format', 'json', '-p', prompt]
    assert len(subprocess.list2cmdline(command)) < 29000
    env = os.environ.copy()
    env['CI'] = 'true'
    env['NO_COLOR'] = '1'
    started = datetime.now(timezone.utc).isoformat()
    tick = time.monotonic()
    with (HERE / (args.name + '.stdout.json')).open('wb') as out, \
            (HERE / (args.name + '.stderr.txt')).open('wb') as err:
        proc = subprocess.Popen(command, cwd=ROOT, env=env, stdin=subprocess.DEVNULL,
                                stdout=out, stderr=err)
        timed_out = False
        try:
            code = proc.wait(timeout=args.seconds)
        except subprocess.TimeoutExpired:
            timed_out = True
            subprocess.run(['taskkill', '/PID', str(proc.pid), '/T', '/F'],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            proc.wait()
            code = 124
    report = dict(started_utc=started, ended_utc=datetime.now(timezone.utc).isoformat(),
                  seconds=time.monotonic()-tick, exit_code=code, timed_out=timed_out,
                  requested_model='Qwen3.8-Max', tools_disabled=True,
                  requested_thinking=args.thinking,
                  scope='Supplied prompt only; no independent compilation or repository access')
    (HERE / (args.name + '-result.json')).write_text(
        json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
