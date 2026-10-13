"""Bounded local-model authoring with shared verified results and serialized review."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone, timedelta
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request

import prove

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / 'theory/jin_wishart_formalization'
PYTHON = Path(r'D:\miniconda3\python.exe')
OLLAMA = Path(r'D:\Ollama\ollama.exe')
LEAN = ROOT / '.tools/elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean.exe'
MODEL = 'deepseek-prover-v2:7b'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def utcnow():
    return datetime.now(timezone.utc)


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2), encoding='utf-8')
    os.replace(temporary, path)


def audited(diagnostic, name):
    if 'sorryAx' in diagnostic or "uses 'sorry'" in diagnostic:
        return False
    if f"'{name}' does not depend on any axioms" in diagnostic:
        return True
    match = re.search(re.escape(f"'{name}' depends on axioms:") + r'\s*\[([^\]]*)\]', diagnostic)
    return bool(match) and set(x.strip() for x in match[1].split(',') if x.strip()) <= ALLOWED_AXIOMS


def remaining(deadline):
    return max(0.0, (deadline - utcnow()).total_seconds())


def bounded(command, log, deadline, timeout, env=None, cwd=None):
    """Only kill the directly launched child; never enumerate unrelated processes."""
    with log.open('w', encoding='utf-8') as stream:
        child = subprocess.Popen(command, stdout=stream, stderr=subprocess.STDOUT,
                                 env=env, cwd=cwd, creationflags=subprocess.CREATE_NO_WINDOW)
        try:
            child.wait(timeout=min(timeout, max(0.01, remaining(deadline))))
            return child.returncode
        except subprocess.TimeoutExpired:
            child.kill()
            child.wait(timeout=10)
            return 124


def unload():
    try:
        # A Windows app launcher named ollama.exe can ignore CLI arguments and
        # open a GUI. The local API unloads only our named model, without a prompt.
        request = urllib.request.Request(
            'http://127.0.0.1:11434/api/generate',
            data=json.dumps({'model': MODEL, 'keep_alive': 0}).encode('utf-8'),
            headers={'Content-Type': 'application/json'},
        )
        with urllib.request.urlopen(request, timeout=10) as connection:
            response = json.loads(connection.read())
        return response.get('done') is True and response.get('done_reason') == 'unload'
    except (OSError, urllib.error.URLError, ValueError):
        return False


def worker(args):
    result = prove.generate(Path(args.prompt).read_text(encoding='utf-8'), MODEL,
                            args.max_tokens, args.seed)
    write_json(Path(args.response), result)
    return 0


def run(args):
    session = Path(args.session).resolve()
    session.mkdir(parents=True, exist_ok=True)
    lock = session / 'runner.lock'
    try:
        descriptor = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError:
        raise SystemExit('Session already has a runner lock; do not launch a duplicate.')
    os.write(descriptor, str(os.getpid()).encode())
    os.close(descriptor)
    work = session / 'work'
    # Lean resolves a package root once, rather than falling through per module.
    # Put our isolated new submodules alongside the existing project cache,
    # so a partial JinWishartFormalization directory cannot shadow its imports.
    library = PROJECT / '.lake/build/lib/lean'
    library.mkdir(exist_ok=True)
    env = os.environ.copy()
    env['ELAN_HOME'] = str(ROOT / '.tools/elan')
    packages = PROJECT / '.lake/packages'
    paths = [library] + [
        p / '.lake/build/lib/lean' for p in packages.iterdir() if p.is_dir()]
    env['LEAN_PATH'] = os.pathsep.join(str(p) for p in paths if p.exists())
    start = utcnow()
    deadline = start + timedelta(seconds=args.duration)
    state = {'pid': os.getpid(), 'model': MODEL, 'started_utc': start.isoformat(),
             'deadline_utc': deadline.isoformat(), 'status': 'RUNNING', 'phase': 'STARTING',
             'attempts': 0, 'accepted': {}, 'blocked': {}, 'current_card': None,
             'role': 'DeepSeek authors density; Codex authors support and reviews; verified results are shared.',
             'module_prefix': args.module_prefix}
    if args.resume:
        previous = json.loads((session / 'state.json').read_text(encoding='utf-8'))
        deadline = datetime.fromisoformat(previous['deadline_utc'])
        if remaining(deadline) <= 0:
            raise ValueError('Cannot resume an expired window')
        state.update(previous)
        state.update(pid=os.getpid(), status='RUNNING', phase='RESUMING_AFTER_ENVIRONMENT_REPAIR',
                     blocked={}, environment_repaired=True,
                     recovery_reason='Partial library root shadowed the existing project cache')
        state.pop('finished_utc', None)
        state.pop('model_stop_succeeded', None)

    def save():
        state['updated_utc'] = utcnow().isoformat()
        write_json(session / 'state.json', state)

    def event(value):
        with (session / 'events.jsonl').open('a', encoding='utf-8') as stream:
            stream.write(json.dumps({'utc': utcnow().isoformat(), **value}, ensure_ascii=False) + '\n')

    def shared():
        path = session / 'shared.json'
        return json.loads(path.read_text(encoding='utf-8')) if path.exists() else {}

    def compute(command, log, timeout, env=None, cwd=None):
        gate = session / 'compute.lock'
        while remaining(deadline) > 0 and not (session / 'STOP').exists():
            if (session / 'CODEX_REVIEW').exists():
                time.sleep(min(0.25, remaining(deadline)))
                continue
            try:
                descriptor = os.open(gate, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            except FileExistsError:
                time.sleep(min(0.25, remaining(deadline)))
                continue
            os.write(descriptor, str(os.getpid()).encode())
            os.close(descriptor)
            try:
                return bounded(command, log, deadline, timeout, env, cwd)
            finally:
                if '--worker' in command:
                    # A timed-out HTTP client can leave server-side generation alive.
                    # Stop/unload our model before releasing the compute gate to Lean.
                    unload()
                gate.unlink()
        return 124

    try:
        save()
        event({'event': 'RESUME' if args.resume else 'START', 'deadline': deadline.isoformat()})
        while remaining(deadline) > 0 and not (session / 'STOP').exists():
            context = Path(args.context).read_text(encoding='utf-8')
            queue = json.loads(Path(args.queue).read_text(encoding='utf-8'))
            exchanged = shared()
            epoch = sorted(set(state['accepted']) | set(exchanged))
            eligible = [card for card in queue if card['id'] not in state['accepted']
                        and card['id'] not in exchanged
                        and all(dep in epoch for dep in card.get('requires', []))
                        and state['blocked'].get(card['id']) != epoch]
            if not eligible:
                proposal_epoch = json.dumps([epoch, [c['id'] for c in queue]], sort_keys=True)
                if state.get('proposal_epoch') != proposal_epoch and remaining(deadline) > 30:
                    state['phase'] = 'LOCAL_MODEL_PLANNING_SUBTASKS'
                    save()
                    proposal_dir = session / 'proposals' / str(len(state['blocked']))
                    proposal_dir.mkdir(parents=True, exist_ok=True)
                    proposal_prompt = ('You are the local mathematical author. All eligible cards '
                        'failed three attempts. Propose THREE smaller Lean theorem statements '
                        'that directly split the remaining Wishart density/support blockers. '
                        'Explain dependencies and do not weaken the original target or repeat '
                        'an already checked theorem. Statements only, no proofs. Codex must review '
                        'your proposals before execution.\n' + context + '\nChecked cards: ' +
                        ', '.join(epoch) + '\nBlocked cards:\n' + '\n'.join(
                            Path(c['source']).read_text(encoding='utf-8') for c in queue
                            if c['id'] in state['blocked'])[:12000])
                    (proposal_dir / 'prompt.txt').write_text(proposal_prompt, encoding='utf-8')
                    compute([str(PYTHON), str(Path(__file__).resolve()), '--worker',
                        '--prompt', str(proposal_dir / 'prompt.txt'), '--response',
                        str(proposal_dir / 'response.json'), '--seed', str(1000+state['attempts']),
                        '--max-tokens', '1536'], proposal_dir / 'generation.txt', 180)
                    state['proposal_epoch'] = proposal_epoch
                    event({'event': 'SUBTASK_PROPOSALS_READY', 'path': str(proposal_dir)})
                # Review heartbeat may add genuinely new decomposed targets or retrieved context.
                state['phase'] = 'WAITING_FOR_TASK_REVIEW'
                state['current_card'] = None
                save()
                time.sleep(min(5, remaining(deadline)))
                continue
            card = eligible[0]
            state['current_card'] = card['id']
            source = Path(card['source']).read_text(encoding='utf-8')
            hole = re.search(r'(?m)^([ \t]*)sorry[ \t]*\s*\Z', source)
            names = re.findall(r'(?m)^theorem\s+([A-Za-z_][A-Za-z_0-9]*)\b', source)
            if (not hole or len(re.findall(r'\bsorry\b', source)) != 1 or len(names) != 1
                or re.search(r'\b(axiom|constant|unsafe|admit|native_decide)\b', source)):
                raise ValueError('Task template must contain one final hole and one named theorem')
            name = names[0]
            feedback = ''
            for attempt in range(1, 4):
                if remaining(deadline) < 5 or (session / 'STOP').exists():
                    break
                state['attempts'] += 1
                number = state['attempts']
                attempt_dir = session / 'attempts' / f'{number:04d}-{card["id"]}'
                attempt_dir.mkdir(parents=True)
                # Reload exchanges between attempts, including a successful partner lemma
                # delivered while this model was generating its previous candidate.
                dependencies = {**shared(), **state['accepted']}
                if 'use' in card:
                    needed = set(card['use']) | set(card.get('requires', []))
                    dependencies = {k: v for k, v in dependencies.items() if k in needed}
                dependency_imports = ''.join('import ' + module + '\n'
                    for module in dict.fromkeys(d['module'] for d in dependencies.values()))
                dependency_declarations = '\n'.join(d['statement'] for d in dependencies.values())
                messages = session / 'messages.md'
                exchange_text = messages.read_text(encoding='utf-8') if messages.exists() else ''
                context = Path(args.context).read_text(encoding='utf-8')
                prompt = ('Continue the Wishart research using this exact Lean 4 target. '
                          'You author density proofs; Codex authors support proofs and reviews. '
                          'Use the shared kernel-checked results and reply to the latest exchange. '
                          'Return ONE fenced lean4 block of tactics for the final hole. '
                          'Do not repeat the theorem, change hypotheses, invent names, use '
                          'placeholders, native_decide, new axioms, or metaprogramming.\n\n' +
                          context + '\nPartner exchange:\n' + exchange_text[-8000:] +
                          '\n\nCARD: ' + card['purpose'] + '\n' + card.get('assets', '') +
                          '\nVerified dependencies:\n' + dependency_declarations +
                          '\n\n```lean4\n' + dependency_imports + source + '\n```\n' + feedback)
                (attempt_dir / 'prompt.txt').write_text(prompt, encoding='utf-8')
                state['phase'] = 'LOCAL_MODEL_GENERATING'
                save()
                event({'event': 'GENERATE', 'card': card['id'], 'attempt': number})
                response_path = attempt_dir / 'response.json'
                code = compute([str(PYTHON), str(Path(__file__).resolve()), '--worker',
                                '--prompt', str(attempt_dir / 'prompt.txt'), '--response',
                                str(response_path), '--seed', str(29 + number),
                                '--max-tokens', str(args.max_tokens)],
                               attempt_dir / 'generation.txt', 300)
                if code or not response_path.exists():
                    event({'event': 'GENERATION_INTERRUPTED', 'card': card['id'], 'exit': code})
                    unload()
                    if remaining(deadline) <= 0:
                        break
                    feedback = '\nPrevious generation failed or timed out. Give a complete shorter proof.'
                    continue
                response = json.loads(response_path.read_text(encoding='utf-8'))
                try:
                    if response.get('done_reason') == 'length':
                        raise ValueError('truncated generation')
                    body = prove.proof_body(response['response'])
                    if re.search(r'\b(native_decide|set_option|elab|macro|run_elab|implemented_by|extern)\b|#', body):
                        raise ValueError('unchecked computation, commands, or metaprogramming')
                except ValueError as error:
                    event({'event': 'OUTPUT_REJECTED', 'card': card['id'], 'reason': str(error)})
                    feedback = '\nReviewer rejected the output: ' + str(error) + '. Tactics only, no placeholders.'
                    continue
                candidate = dependency_imports + source[:hole.start()] + \
                    '\n'.join(hole.group(1) + line for line in body.splitlines()) + \
                    '\n\n#print axioms ' + name + '\n'
                module = args.module_prefix + '.' + card['id']
                candidate_path = work / Path(module.replace('.', '/') + '.lean')
                candidate_path.parent.mkdir(parents=True, exist_ok=True)
                candidate_path.write_text(candidate, encoding='utf-8')
                (attempt_dir / 'candidate.lean').write_text(candidate, encoding='utf-8')
                olean = library / Path(module.replace('.', '/') + '.olean')
                olean.parent.mkdir(parents=True, exist_ok=True)
                state['phase'] = 'LEAN_REVIEW'
                save()
                diagnostic_path = attempt_dir / 'check.txt'
                code = compute([str(LEAN), '-DautoImplicit=false', '-j1', '-R', str(work),
                                '-o', str(olean), str(candidate_path)],
                               diagnostic_path, 180, env, PROJECT)
                diagnostic = (diagnostic_path.read_text(encoding='utf-8', errors='replace')
                              if diagnostic_path.exists() else 'Check not started before stop/deadline.')
                if code == 0 and audited(diagnostic, name):
                    accepted = session / 'accepted' / (card['id'] + '.lean')
                    accepted.parent.mkdir(exist_ok=True)
                    accepted.write_text(candidate, encoding='utf-8')
                    state['accepted'][card['id']] = {'module': module, 'path': str(accepted),
                        'statement': source[:hole.start()].rsplit(':= by', 1)[0].strip(), 'attempt': number,
                        'sha256': hashlib.sha256(candidate.encode()).hexdigest(),
                        'semantic_review': 'PENDING_CODEX_REVIEW', 'author': MODEL,
                        'provenance': card.get('provenance', 'Local generation with retrieved partner context')}
                    event({'event': 'LEAN_CHECK_PASSED', 'card': card['id'], 'attempt': number})
                    save()
                    break
                event({'event': 'LEAN_REJECTED', 'card': card['id'], 'attempt': number, 'exit': code})
                feedback = ('\nYour previous tactics were:\n```lean4\n' + body[-5000:] +
                            '\n```\nActual Lean diagnostics:\n' + diagnostic[-7000:] +
                            '\nRepair the proof body; the original statement remains unchanged.')
            if card['id'] not in state['accepted']:
                # Three failures block this card until genuinely new checked context is available.
                state['blocked'][card['id']] = epoch
                event({'event': 'CARD_BLOCKED', 'card': card['id']})
                save()
        state['status'] = 'STOPPED_BY_USER' if (session / 'STOP').exists() else 'DEADLINE_REACHED'
        state['phase'] = 'FINISHED'
    except Exception as error:
        state['status'] = 'FAILED'
        state['error'] = repr(error)
        state['phase'] = 'FINISHED'
        raise
    finally:
        state['model_stop_succeeded'] = unload()
        state['finished_utc'] = utcnow().isoformat()
        save()
        event({'event': 'FINISH', 'status': state['status'], 'accepted': list(state['accepted'])})
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--worker', action='store_true')
    parser.add_argument('--prompt')
    parser.add_argument('--response')
    parser.add_argument('--seed', type=int, default=30)
    parser.add_argument('--max-tokens', type=int, default=3072)
    parser.add_argument('--session')
    parser.add_argument('--queue')
    parser.add_argument('--context')
    parser.add_argument('--duration', type=int, default=3600)
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--module-prefix', default='JinWishartFormalization.DeepSeekHour20261010')
    args = parser.parse_args()
    if not 1 <= args.duration <= 3600:
        parser.error('duration must be 1..3600 seconds')
    if not re.fullmatch(r'[A-Za-z][A-Za-z_0-9]*(\.[A-Za-z][A-Za-z_0-9]*)*', args.module_prefix):
        parser.error('module-prefix must be a Lean module path')
    return worker(args) if args.worker else run(args)


if __name__ == '__main__':
    sys.stdout.reconfigure(encoding='utf-8', errors='backslashreplace')
    raise SystemExit(main())
