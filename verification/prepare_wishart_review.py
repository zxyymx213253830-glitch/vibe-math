"""Prepare a byte-linked independent review handoff; never certify review."""
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
        "status": "READY_FOR_INDEPENDENT_REVIEW_NOT_REVIEWED",
        "entries": entries,
        "manuscript": {"path": "theory/wishart_paper/main.tex", "sha256": sha(PAPER / "main.tex")},
        "sources": {name: {**sources[name], "imports": dependencies[name],
                              "theorems": re.findall(r"^(?:theorem|lemma)\s+(\w+)", code[name], re.M)}
                    for name in sorted(closure)},
        "instruction": "AGENTS P4, issues only, different model family; human semantic acceptance is separate",
    }
    (ROOT / "verification/WISHART_P4_REVIEW_MANIFEST.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    raw = ROOT / ".tools/publication-acceptance-20261016/claude-p4"
    evidence = ROOT / "verification/publication_checks/independent-review-20261016"
    evidence.mkdir(exist_ok=True)
    for filename in ["request.txt", "response.json", "stderr.txt", "invocation.json"]:
        shutil.copy2(raw / filename, evidence / filename)
    response = json.loads((evidence / "response.json").read_text(encoding="utf-8"))
    result = {
        "status": "BLOCKED_EXTERNAL_REVIEW_NOT_DELIVERED",
        "reason": response.get("result"), "api_error_status": response.get("api_error_status"),
        "reported_model_usage": response.get("modelUsage"),
        "usable_issue_report": False, "completed_independent_review": False,
        "human_review": "PENDING [需人工审查]",
        "automatic_paid_retries": 0,
        "raw_evidence": {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(evidence.iterdir())},
        "review_snapshot_sha256": sha(ROOT / "verification/WISHART_P4_REVIEW_MANIFEST.json"),
    }
    (ROOT / "verification/WISHART_INDEPENDENT_REVIEW_STATUS.json").write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Prepared {len(closure)} source files for independent review; no review success claimed")


if __name__ == "__main__":
    main()
