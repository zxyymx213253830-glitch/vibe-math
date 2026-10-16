"""Re-elaborate project sources in topological order into fresh Lean output.

Uses the existing compute gate and pinned toolchain, with external package
caches. This is NOT a clean rebuild of mathlib and NOT a full Lake build.
No source/output from a previous project build is used for project imports.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "theory/jin_wishart_formalization"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--session", required=True, type=Path)
    parser.add_argument("--resume", action="store_true", help="Reuse only successful, unchanged source outputs")
    parser.add_argument("--gate-session", type=Path, help="New acceptance authorization/compute gate, retaining the prior output campaign")
    args = parser.parse_args()
    session = args.session.resolve()
    gate_session = args.gate_session.resolve() if args.gate_session else session
    library = session / "fresh-project-library"
    if library.exists() and not args.resume:
        raise SystemExit("Fresh output already exists; choose a new session, do not overwrite evidence")
    library.mkdir(parents=True, exist_ok=args.resume)
    modules = {p.relative_to(PROJECT).with_suffix("").as_posix().replace("/", "."): p
               for p in (PROJECT / "JinWishartFormalization").rglob("*.lean")}
    modules["JinWishartFormalization"] = PROJECT / "JinWishartFormalization.lean"
    imports = {name: re.findall(r"^import\s+(\S+)", path.read_text(encoding="utf-8"), re.M)
               for name, path in modules.items()}
    ordered, visiting, visited = [], set(), set()

    def visit(name):
        if name in visited:
            return
        if name in visiting:
            raise RuntimeError("Cyclic imports: " + name)
        visiting.add(name)
        for dep in imports[name]:
            if dep in modules:
                visit(dep)
            elif dep.startswith("JinWishartFormalization"):
                raise RuntimeError("Missing project import: " + dep)
        visiting.remove(name)
        visited.add(name)
        ordered.append(name)

    for name in sorted(modules):
        visit(name)
    records = []
    report_path = ROOT / "verification/WISHART_PUBLICATION_REBUILD.json"
    started = datetime.now(timezone.utc).isoformat()
    previous = json.loads(report_path.read_text(encoding="utf-8")) if args.resume else {}
    if args.resume and previous.get("session") != session.relative_to(ROOT).as_posix():
        raise SystemExit("Resume requires the same recorded campaign session")
    campaign_started = previous.get("campaign_started_utc", started)
    batches = list(previous.get("batches", []))
    current_batch = {"started_utc": started, "finished_utc": None,
                     "compiled_modules": 0, "reused_modules": 0,
                     "authorization_session": gate_session.relative_to(ROOT).as_posix()}
    batches.append(current_batch)
    prior = {item["module"]: item for item in previous.get("resume_record_pool_not_current_validation", [])}
    prior.update({item["module"]: item for item in previous.get("records", [])})
    history = list(previous.get("failed_attempts", []))
    history.extend(item for item in previous.get("records", []) if item["exit_code"] != 0)
    rebuilt = set()
    for index, name in enumerate(ordered):
        source = modules[name]
        log = session / (name + ".txt")
        before = hashlib.sha256(source.read_bytes()).hexdigest()
        cached = prior.get(name)
        olean = library / (name.replace(".", "/") + ".olean")
        dependencies_rebuilt = any(dep in rebuilt for dep in imports[name])
        output_matches = (olean.exists() and cached and cached.get("olean_sha256") ==
                          hashlib.sha256(olean.read_bytes()).hexdigest())
        if cached and cached["exit_code"] == 0 and cached["sha256"] == before and output_matches and not dependencies_rebuilt:
            # These outputs were produced by the prior fresh-source pass, not
            # copied from the project's ordinary build cache.
            records.append(cached)
            current_batch["reused_modules"] += 1
            continue
        rebuilt.add(name)
        if log.exists():
            archived = log.with_name(log.stem + ".previous-" + hashlib.sha256(log.read_bytes()).hexdigest()[:12] + ".txt")
            if not archived.exists():
                archived.write_bytes(log.read_bytes())
        module_started = datetime.now(timezone.utc).isoformat()
        timer = time.monotonic()
        result = subprocess.run([sys.executable,
            str(ROOT / "tools/deepseek_prover/collaborative_check.py"),
            "--session", str(gate_session), "--source", str(source), "--module", name,
            "--log", str(log), "--library", str(library)])
        elapsed = time.monotonic() - timer
        module_finished = datetime.now(timezone.utc).isoformat()
        current_batch["compiled_modules"] += 1
        after = hashlib.sha256(source.read_bytes()).hexdigest()
        record = {"module": name, "source": source.relative_to(ROOT).as_posix(),
                  "sha256": before, "exit_code": result.returncode,
                  "started_utc": module_started, "finished_utc": module_finished,
                  "wall_seconds": round(elapsed, 6),
                  "timing_scope": "helper process including gate wait and Lean; wall clock, not CPU",
                  "source_unchanged": before == after,
                  "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest() if log.exists() else None,
                  "olean_sha256": hashlib.sha256(olean.read_bytes()).hexdigest() if olean.exists() else None}
        records.append(record)
        passed = result.returncode == 0 and before == after
        done = len(records) == len(ordered)
        updated = datetime.now(timezone.utc).isoformat()
        current_batch["finished_utc"] = updated
        report = {"schema_version": 2, "campaign_started_utc": campaign_started,
                  "started_utc": campaign_started, "updated_utc": updated,
                  "campaign_wall_seconds": (datetime.fromisoformat(updated)-datetime.fromisoformat(campaign_started)).total_seconds(),
                  "compiled_module_wall_seconds_sum": round(sum(r.get("wall_seconds", 0) for r in records), 6),
                  "batches": batches, "session": session.relative_to(ROOT).as_posix(),
                  "method": "fresh project-source elaboration, cached pinned external packages, serial shared gate",
                  "full_Lake_build": "NOT_RUN", "mathlib_rebuilt_from_source": False,
                  "status": "PASS" if done and passed else "RUNNING" if passed else "FAILED",
                  "total_modules": len(ordered), "checked_modules": len(records),
                  "toolchain": (PROJECT / "lean-toolchain").read_text().strip(),
                  "manifest_sha256": hashlib.sha256((PROJECT / "lake-manifest.json").read_bytes()).hexdigest(),
                  "records": records}
        report["initial_started_utc"] = previous.get("initial_started_utc", previous.get("started_utc", started))
        report["failed_attempts"] = history
        if not done:
            # Preserve the unvisited suffix of a prior complete campaign.
            # These are cache candidates only; each hash/dependency is checked
            # before reuse. They do not count toward this pass's checked total.
            report["resume_record_pool_not_current_validation"] = list(prior.values())
        report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(f"{index+1}/{len(ordered)} {name}: {'PASS' if passed else 'FAILED'}", flush=True)
        if not passed:
            return 1
    # A reused suffix (or an entirely reused validation batch) must also
    # reach a terminal report; the last compilation may not be the last module.
    final = json.loads(report_path.read_text(encoding="utf-8"))
    updated = datetime.now(timezone.utc).isoformat()
    current_batch["finished_utc"] = updated
    final.update({"status": "PASS", "records": records, "checked_modules": len(records),
                  "total_modules": len(ordered), "batches": batches, "updated_utc": updated,
                  "compiled_module_wall_seconds_sum": round(sum(r.get("wall_seconds", 0) for r in records), 6),
                  "campaign_wall_seconds": (datetime.fromisoformat(updated)-datetime.fromisoformat(campaign_started)).total_seconds()})
    final.pop("resume_record_pool_not_current_validation", None)
    report_path.write_text(json.dumps(final, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
