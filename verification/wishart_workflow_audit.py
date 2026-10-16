"""Export recorded local-prover outcomes and provenance, not a benchmark."""
from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[1]
SESSION = ROOT / ".tools/deepseek-hour/collaboration-round3-20261011"


def main() -> None:
    evidence = ROOT / "verification/workflow_evidence/round3"
    evidence.mkdir(parents=True, exist_ok=True)
    events_path = SESSION / "events.jsonl"
    events = [json.loads(line) for line in events_path.read_text(encoding="utf-8").splitlines() if line]
    counts = Counter(event["event"] for event in events)
    assert (counts["GENERATE"], counts["LEAN_CHECK_PASSED"], counts["LEAN_REJECTED"],
            counts["OUTPUT_REJECTED"]) == (38, 2, 29, 7)
    shutil.copy2(events_path, evidence / "events.jsonl")
    records = []
    for response in sorted(SESSION.glob("*p4-response.json")):
        prompt = response.with_name(response.name.replace("-response.json", "-prompt.txt"))
        assert prompt.exists()
        for source in [prompt, response]:
            shutil.copy2(source, evidence / source.name)
        value = json.loads(response.read_text(encoding="utf-8"))
        records.append({"request": (evidence / prompt.name).relative_to(ROOT).as_posix(),
                        "request_sha256": hashlib.sha256(prompt.read_bytes()).hexdigest(),
                        "response": (evidence / response.name).relative_to(ROOT).as_posix(),
                        "response_sha256": hashlib.sha256(response.read_bytes()).hexdigest(),
                        "verdict": "NONRESPONSIVE_NOT_VALID_REVIEW",
                        "response_excerpt": value.get("response", "")[:220]})
    assert len(records) == 5
    result = {"scope": "2026-10-11 round3 runner calls only; adaptively guided observational record",
              "model": "deepseek-prover-v2:7b", "generations": 38,
              "kernel_passed": 2, "lean_rejected": 29, "output_rejected_before_check": 7,
              "accepted_cards": [e["card"] for e in events if e["event"] == "LEAN_CHECK_PASSED"],
              "additional_manual_author_calls_excluded": 2,
              "additional_manual_author_calls_passed": 0,
              "manual_call_count_source": "notes/DEEPSEEK_CODEX_ROUND3_SUMMARY_20261011.md",
              "p4_requests_separate_from_generation_denominator": 5, "usable_p4_reviews": 0,
              "runner_finish": events[-1],
              "runner_failure_cause": "Malformed task template; not a full-hour throughput benchmark",
              "event_log": (evidence / "events.jsonl").relative_to(ROOT).as_posix(),
              "event_log_sha256": hashlib.sha256(events_path.read_bytes()).hexdigest(),
              "p4": records, "semantic_review": "Still pending; output review is not proof review"}
    (ROOT / "verification/WISHART_WORKFLOW_AUDIT.json").write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print("PASS: 38 runner calls = 2 kernel pass + 29 Lean rejects + 7 output rejects; 5 genuine P4 responses")


if __name__ == "__main__":
    main()
