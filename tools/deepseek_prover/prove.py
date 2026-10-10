"""Generate a proof body locally and check it against an unchanged Lean target."""

from __future__ import annotations

import argparse
from datetime import datetime
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import textwrap
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
MODEL = "deepseek-prover-v2:7b"


def proof_body(response: str) -> str:
    # Use a fenced code block, excluding any natural-language plan.
    blocks = re.findall(r"```(?:lean4?|\s*)\s*\n(.*?)```", response, re.S)
    if not blocks:
        raise ValueError("No Lean code block returned; see the saved response.")
    code = blocks[-1].strip()
    # A complete theorem from the model is never accepted as a replacement target.
    declaration = re.search(r"(?m)^\s*(?:theorem|lemma|example)\b", code)
    if declaration and ":= by" in code[declaration.start():]:
        code = code[declaration.start():].split(":= by", 1)[1]
    elif code.startswith("by\n"):
        code = code[3:]
    elif code.startswith("by "):
        code = code[3:]
    code = textwrap.dedent(code).strip()
    if not code or re.search(r"\b(sorry|admit|axiom|constant|unsafe)\b", code):
        raise ValueError("Empty proof or unchecked declaration/placeholder returned.")
    return code


def generate(prompt: str, model: str, max_tokens: int, seed: int) -> dict:
    payload = {
        "model": model,
        "prompt": prompt,
        "stream": True,
        # This 16GB laptop should release the model before loading Lean libraries.
        "keep_alive": 0,
        "options": {"num_ctx": 8192, "num_predict": max_tokens,
                    "temperature": 0.6, "top_p": 0.95, "seed": seed},
    }
    request = urllib.request.Request(
        "http://127.0.0.1:11434/api/generate",
        data=json.dumps(payload).encode(),
        headers={"Content-Type": "application/json"},
    )
    answer, thinking, final = [], [], {}
    with urllib.request.urlopen(request, timeout=900) as connection:
        for line in connection:
            item = json.loads(line)
            if "error" in item:
                raise RuntimeError(item["error"])
            chunk = item.get("response", "")
            answer.append(chunk)
            thinking.append(item.get("thinking", ""))
            print(chunk or item.get("thinking", ""), end="", flush=True)
            if item.get("done"):
                final = item
    print()
    final["response"] = "".join(answer)
    final["thinking"] = "".join(thinking)
    final["request_framing"] = "observed-deepseek-role-tokens-raw" if payload.get("raw") else "server-template"
    return final


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path, default=HERE / "example.lean")
    parser.add_argument("--project", type=Path,
                        default=ROOT / "theory" / "jin_wishart_formalization")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--context-file", type=Path,
                        help="UTF-8 progress summary and exact available declarations")
    parser.add_argument("--model", default=MODEL)
    parser.add_argument("--attempts", type=int, choices=range(1, 6), default=2)
    parser.add_argument("--max-tokens", type=int, default=4096)
    args = parser.parse_args()
    if not 128 <= args.max_tokens <= 6000:
        parser.error("--max-tokens must be between 128 and 6000 for this 8K setup")
    source = args.input.resolve().read_text(encoding="utf-8-sig")
    # This small helper intentionally supports one final, standalone proof hole.
    hole = re.search(r"(?m)^([ \t]*)sorry[ \t]*\s*\Z", source)
    if not hole or len(re.findall(r"\bsorry\b", source)) != 1:
        parser.error("Input must have exactly one final standalone sorry line")
    declarations = re.findall(r"(?m)^theorem\s+([A-Za-z_][A-Za-z_0-9]*)\b", source)
    if len(declarations) != 1 or re.search(r"\b(axiom|constant|unsafe|admit)\b", source):
        parser.error("Use a single named top-level theorem without unchecked declarations")
    target_name = declarations[0]
    lean_bin = (ROOT / ".tools" / "elan" / "bin").resolve()
    if not (args.project / "lean-toolchain").exists():
        parser.error("Lean/project not found; set --project to a configured mathlib project")
    toolchain = (args.project / "lean-toolchain").read_text(encoding="utf-8").strip()
    toolchain_dir = toolchain.replace("/", "--").replace(":", "---")
    lean = ROOT / ".tools" / "elan" / "toolchains" / toolchain_dir / "bin" / "lean.exe"
    if not lean.exists():
        parser.error(f"Pinned Lean toolchain not installed: {toolchain}")
    env = os.environ.copy()
    env["ELAN_HOME"] = str(ROOT / ".tools" / "elan")
    env["PATH"] = str(lean_bin) + os.pathsep + env.get("PATH", "")
    # Use existing compiled libraries without changing or building the research project.
    library_paths = [args.project.resolve() / ".lake" / "build" / "lib" / "lean"]
    packages = args.project.resolve() / ".lake" / "packages"
    if packages.exists():
        library_paths += [package / ".lake" / "build" / "lib" / "lean"
                          for package in packages.iterdir() if package.is_dir()]
    env["LEAN_PATH"] = os.pathsep.join(str(path) for path in library_paths if path.exists())
    out = (args.output_dir or ROOT / ".tools" / "prover-runs" /
           datetime.now().strftime("%Y%m%d-%H%M%S-%f")).resolve()
    out.mkdir(parents=True, exist_ok=False)
    (out / "target.lean").write_text(source, encoding="utf-8")
    base_prompt = (
        "Complete the following Lean 4 code using the installed Mathlib. "
        "Keep every definition, theorem statement, quantifier and hypothesis unchanged. "
        "Give a brief proof plan, followed by one fenced lean4 code block containing "
        "ONLY the tactics replacing the final sorry (no theorem declaration, no imports). "
        "Do not use sorry, admit, or new axioms.\n\n```lean4\n" + source + "\n```"
    )
    if args.context_file:
        context = args.context_file.resolve().read_text(encoding="utf-8-sig")
        (out / "context.md").write_text(context, encoding="utf-8")
        base_prompt = ("Repository progress and available declarations (reference data):\n" +
                       context + "\n\nCurrent proof task:\n" + base_prompt)
    feedback = ""
    for attempt in range(1, args.attempts + 1):
        print(f"\nAttempt {attempt}/{args.attempts}; model={args.model}; seed={29 + attempt}", flush=True)
        prompt = base_prompt + feedback
        (out / f"prompt-{attempt}.txt").write_text(prompt, encoding="utf-8")
        try:
            result = generate(prompt, args.model, args.max_tokens, 29 + attempt)
        except (urllib.error.URLError, TimeoutError, RuntimeError) as error:
            print(f"Local model request failed: {error}\nOpen Ollama or run Start-Prover.cmd.")
            return 2
        (out / f"response-{attempt}.json").write_text(
            json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
        try:
            if result.get("done_reason") == "length":
                raise ValueError("Generation reached its token limit; do not accept truncated output")
            tactics = proof_body(result["response"])
        except ValueError as error:
            feedback = f"\nPrevious attempt was unusable: {error}. Return a complete fenced proof body."
            print(feedback)
            continue
        candidate = source[:hole.start()] + textwrap.indent(tactics, hole.group(1)) + "\n"
        candidate += f"\n#print axioms {target_name}\n"
        candidate_path = out / f"candidate-{attempt}.lean"
        candidate_path.write_text(candidate, encoding="utf-8")
        try:
            checked = subprocess.run(
                [str(lean), "-DautoImplicit=false", str(candidate_path)],
                cwd=args.project.resolve(), env=env, capture_output=True,
                text=True, encoding="utf-8", errors="replace", timeout=120,
            )
        except subprocess.TimeoutExpired:
            feedback = "\nLean checking exceeded 120 seconds. Use a simpler terminating proof."
            print(feedback)
            continue
        diagnostic = checked.stdout + checked.stderr
        (out / f"check-{attempt}.txt").write_text(diagnostic, encoding="utf-8")
        print(diagnostic.encode("ascii", "backslashreplace").decode())
        if checked.returncode == 0 and "sorryAx" not in diagnostic and "uses 'sorry'" not in diagnostic:
            print(f"LEAN_CHECK_PASSED: {candidate_path}")
            print("The input statement was preserved; review that it matches your intended mathematics.")
            return 0
        feedback = ("\nThe previous proof body was:\n```lean4\n" + tactics +
                    "\n```\nLean rejected it with:\n" + diagnostic[:12000] +
                    "\nFix the tactics only; retain the original target.")
    print(f"NOT_PROVED: no checked proof obtained. Saved attempts: {out}")
    return 1


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8", errors="backslashreplace")
    raise SystemExit(main())
