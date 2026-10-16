"""Validate the final acceptance snapshot and archives without inventing P4."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import zipfile

from prepare_wishart_publication import ROOT, PAPER, scan_sources, sha


def load(relative):
    return json.loads((ROOT / relative).read_text(encoding="utf-8"))


def main():
    sources, _, _ = scan_sources()
    claims = load("theory/wishart_paper/claims.json")
    binding = load("verification/WISHART_PUBLICATION_AUDIT_BINDING.json")
    rebuild = load("verification/WISHART_PUBLICATION_REBUILD.json")
    qa = load("verification/WISHART_PAPER_PDF_QA.json")
    delivery = load("verification/WISHART_PAPER_DELIVERY.json")
    review = load("verification/WISHART_INDEPENDENT_REVIEW_STATUS.json")
    assert rebuild["status"] == binding["status"] == qa["status"] == "PASS"
    assert sources == binding["project_source_snapshot"] == claims["all_project_sources"]
    assert binding["manuscript"]["sha256"] == qa["manuscript_sha256"] == sha(PAPER / "main.tex")
    assert binding["rebuild_report_sha256"] == sha(ROOT / "verification/WISHART_PUBLICATION_REBUILD.json")
    for field in ["audit_source", "audit_log"]:
        assert binding[field]["sha256"] == sha(ROOT / binding[field]["path"])
    assert len(binding["targets"]) == claims["claims_audit"]["public_declaration_count"]
    assert all(item["printed"] and set(item["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
               for item in binding["printed_axioms"].values())
    assert qa["pdf_sha256"] == sha(ROOT / delivery["pdf"]["path"])
    assert qa["rendered_and_visually_inspected_pages"] == list(range(1, qa["pages"] + 1))
    assert qa["standalone_source_archive_check"]["status"] == "PASS"
    verified_payloads = 0
    for item in delivery["archives"]:
        path = ROOT / item["path"]
        assert sha(path) == item["sha256"]
        with zipfile.ZipFile(path) as archive:
            assert archive.testzip() is None
            if path.name == "wishart_latex_source.zip":
                assert archive.read("main.tex") == (PAPER / "main.tex").read_bytes()
                assert sha(path) == qa["standalone_source_archive_check"]["source_zip_sha256"]
            else:
                for name, digest in json.loads(archive.read("SHA256SUMS.json")).items():
                    assert hashlib.sha256(archive.read(name)).hexdigest() == digest
                    assert (ROOT / name).is_file() and sha(ROOT / name) == digest, (name, "stale payload")
                    verified_payloads += 1
    for path, digest in review["raw_evidence"].items():
        assert sha(ROOT / path) == digest
    result = {
        "checked_utc": datetime.now(timezone.utc).isoformat(),
        "machine_acceptance": "PASS",
        "overall_academic_acceptance": "INCOMPLETE_INDEPENDENT_REVIEW",
        "project_modules": len(sources), "public_declarations_audited": len(binding["targets"]),
        "mapped_paper_claims": len(claims["claims"]), "pdf_pages": qa["pages"],
        "archive_payload_hashes_checked": verified_payloads,
        "source_to_output_to_manuscript_binding": "PASS",
        "pdf_visual_and_standalone_source_compilation": "PASS",
        "full_Lake_build": "NOT_RUN; project-source verification is separately recorded",
        "independent_review": review["status"], "external_failure": review["reason"],
        "semantic_obligations": "[需人工审查] Fubini/skew-product, sample/notation conventions, intrinsic Frobenius volume interpretation",
        "submission_preparation": "Human authorship, license, public release and comprehensive novelty comparison remain separate",
        "evidence_sha256": {p: sha(ROOT / p) for p in [
            "theory/wishart_paper/main.tex", "theory/wishart_paper/claims.json",
            "verification/WISHART_PUBLICATION_REBUILD.json", "verification/WISHART_PUBLICATION_AUDIT_BINDING.json",
            "verification/WISHART_PAPER_PDF_QA.json", "verification/WISHART_PAPER_DELIVERY.json",
            "verification/WISHART_INDEPENDENT_REVIEW_STATUS.json"]},
    }
    (ROOT / "verification/WISHART_ACCEPTANCE.json").write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"PASS machine acceptance: {len(sources)} modules, {len(binding['targets'])} declarations, "
          f"{len(claims['claims'])} mapped claims, {qa['pages']} pages; independent review remains incomplete")


if __name__ == "__main__":
    main()
