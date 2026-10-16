"""Bind an existing scoped Step review and retain its original snapshot."""
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import shutil

from prepare_wishart_publication import ROOT, PAPER, CLAIMS, scan_sources, sha


def main():
    sources, code, dependencies = scan_sources()
    entries = sorted({"JinWishartFormalization." + c[2] for c in CLAIMS})
    closure = set()

    def visit(name):
        if name in closure:
            return
        closure.add(name)
        for dep in dependencies[name]:
            if dep in sources:
                visit(dep)

    for entry in entries:
        visit(entry)
    manifest = {
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "status": "CURRENT_SNAPSHOT_SCOPED_REVIEW_WITH_EDITORIAL_UPDATE",
        "entries": entries,
        "manuscript": {"path": "theory/wishart_paper/main.tex", "sha256": sha(PAPER / "main.tex")},
        "sources": {name: {**sources[name], "imports": dependencies[name],
                              "theorems": re.findall(r"^(?:theorem|lemma)\s+(\w+)", code[name], re.M)}
                    for name in sorted(closure)},
        "instruction": "AGENTS P4, issues only, different model family; human semantic acceptance is separate",
    }
    evidence = ROOT / "verification/publication_checks/step-review-20261016"
    reviewed = evidence / "reviewed-manifest.json"
    snapshot = json.loads(reviewed.read_text(encoding="utf-8"))
    assert all(sha(ROOT / x["path"]) == x["sha256"] for x in snapshot["sources"].values())
    assert snapshot["sources"].keys() == manifest["sources"].keys()
    report = ROOT / "verification/WISHART_P4_REVIEW_RESPONSE_20261016.md"
    assert "Step" in report.read_text(encoding="utf-8")
    manifest["reviewed_snapshot"] = {"path": reviewed.relative_to(ROOT).as_posix(),
                                     "sha256": sha(reviewed), "Lean_sources_unchanged": True,
                                     "editorial_manuscript_update_not_rereviewed": True}
    (ROOT / "verification/WISHART_P4_REVIEW_MANIFEST.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    old_response = ROOT / "verification/publication_checks/independent-review-20261016/response.json"
    response = json.loads(old_response.read_text(encoding="utf-8"))
    raw_paths = list(evidence.iterdir()) + [report,
        ROOT / "notes/ARXIV_SUBMISSION_REVIEW_20261016.md",
        ROOT / "theory/wishart_paper/STEP_REVIEW_DISPOSITION.md"]
    result = {
        "status": "SCOPED_CROSS_FAMILY_REVIEW_COMPLETED_HUMAN_PENDING",
        "reason": "Existing Step-family report delivered; scoped model review is distinct from human signoff",
        "model_family": "Step, as attributed by the existing WorkBuddy report; no new invocation claimed",
        "usable_issue_report": True, "completed_independent_review": True,
        "scope": "32 files fully read, two statement-only; approximately 130 project modules and mathlib not proof-body reviewed",
        "mathematical_errors_reported_in_inspected_scope": 0,
        "Lean_sources_unchanged_from_reviewed_snapshot": True,
        "editorial_updates_after_review": "author, PDF metadata, review status, chart domain and volume/scope clarifications",
        "human_review": "PENDING [需人工审查]",
        "previous_failure": {"result": response.get("result"), "api_error_status": response.get("api_error_status"),
                             "evidence": old_response.relative_to(ROOT).as_posix()},
        "automatic_paid_retries": 0,
        "raw_evidence": {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(raw_paths) if p.is_file()},
        "review_snapshot_sha256": sha(reviewed),
        "current_snapshot_sha256": sha(ROOT / "verification/WISHART_P4_REVIEW_MANIFEST.json"),
    }
    (ROOT / "verification/WISHART_INDEPENDENT_REVIEW_STATUS.json").write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Bound existing scoped Step review to {len(closure)} unchanged sources; human review pending")


if __name__ == "__main__":
    main()
