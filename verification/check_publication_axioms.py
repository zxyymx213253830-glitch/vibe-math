"""Run the expanded axiom audit and bind actual output to the checked snapshot."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from prepare_wishart_publication import ROOT, PAPER, PROJECT, scan_sources, generate_audit_source, sha


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--session", required=True, type=Path)
    args = parser.parse_args()
    session = args.session.resolve()
    sources, code, _ = scan_sources()
    audit, targets = generate_audit_source(code)
    rebuild_path = ROOT / "verification/WISHART_PUBLICATION_REBUILD.json"
    rebuild = json.loads(rebuild_path.read_text(encoding="utf-8"))
    assert rebuild["status"] == "PASS"
    records = {r["module"]: r for r in rebuild["records"]}
    library = session / "fresh-project-library"
    compiled = {}
    for name, source in sources.items():
        assert records[name]["sha256"] == source["sha256"] and records[name]["exit_code"] == 0
        olean = library / (name.replace(".", "/") + ".olean")
        compiled[name] = sha(olean)
        assert compiled[name] == records[name]["olean_sha256"]
    manuscript_sha = sha(PAPER / "main.tex")
    audit_sha = sha(audit)
    log = ROOT / "verification/publication_checks/claims-axioms.txt"
    if log.exists():
        old = log.with_name("claims-axioms-" + sha(log)[:12] + ".txt")
        if not old.exists():
            shutil.copy2(log, old)
    command = [sys.executable, str(ROOT / "tools/deepseek_prover/collaborative_check.py"),
               "--session", str(session), "--source", str(audit), "--root", str(PAPER),
               "--module", "ClaimsCheck", "--library", str(library), "--log", str(log)]
    started = datetime.now(timezone.utc).isoformat()
    timer = time.monotonic()
    result = subprocess.run(command)
    duration = time.monotonic()-timer
    text = log.read_text(encoding="utf-8")
    printed = {}
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name in targets:
        match = re.search(re.escape("'"+name+"' depends on axioms:") + r"\s*\[([^\]]*)\]", text)
        empty = "'"+name+"' does not depend on any axioms" in text
        axioms = {x.strip() for x in match[1].split(",") if x.strip()} if match else set()
        printed[name] = {"printed": bool(match or empty), "axioms": sorted(axioms)}
    after, _, _ = scan_sources()
    unchanged = (after == sources and sha(PAPER / "main.tex") == manuscript_sha and sha(audit) == audit_sha
                 and all(sha(library / (name.replace(".", "/") + ".olean")) == digest for name, digest in compiled.items()))
    passed = result.returncode == 0 and unchanged and all(x["printed"] and set(x["axioms"]) <= allowed for x in printed.values())
    snapshot_digest = hashlib.sha256(json.dumps(sources, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    binding = {"status": "PASS" if passed else "FAILED", "started_utc": started,
               "finished_utc": datetime.now(timezone.utc).isoformat(), "wall_seconds": duration,
               "exit_code": result.returncode, "snapshot_unchanged_during_check": unchanged,
               "project_source_snapshot_sha256": snapshot_digest, "project_source_snapshot": sources,
               "compiled_project_olean_sha256": compiled,
               "audit_source": {"path": audit.relative_to(ROOT).as_posix(), "sha256": audit_sha},
               "audit_log": {"path": log.relative_to(ROOT).as_posix(), "sha256": sha(log)},
               "manuscript": {"path": "theory/wishart_paper/main.tex", "sha256": manuscript_sha},
               "toolchain_sha256": sha(PROJECT / "lean-toolchain"),
               "lake_manifest_sha256": sha(PROJECT / "lake-manifest.json"),
               "rebuild_report_sha256": sha(rebuild_path), "targets": targets,
               "printed_axioms": printed, "semantic_review": "PENDING [需人工审查]"}
    (ROOT / "verification/WISHART_PUBLICATION_AUDIT_BINDING.json").write_text(
        json.dumps(binding, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
    print(f"{'PASS' if passed else 'FAILED'}: {len(targets)} printed declarations bound to source, outputs and manuscript")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
