"""Create local review/source archives; does not publish or select a license."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "theory/wishart_paper"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    claims = json.loads((PAPER / "claims.json").read_text(encoding="utf-8"))
    assert claims["fresh_source_rebuild"]["status"] == "PASS"
    assert claims["claims_audit"]["all_targets_printed_standard_axioms"]
    binding_path = ROOT / "verification/WISHART_PUBLICATION_AUDIT_BINDING.json"
    binding = json.loads(binding_path.read_text(encoding="utf-8"))
    assert binding["status"] == "PASS"
    assert claims["claims_audit"]["binding_sha256"] == sha(binding_path)
    assert binding["manuscript"]["sha256"] == sha(PAPER / "main.tex")
    assert claims["claims_audit"]["log_sha256"] == sha(ROOT / binding["audit_log"]["path"])
    assert binding["rebuild_report_sha256"] == sha(ROOT / "verification/WISHART_PUBLICATION_REBUILD.json")
    for source in claims["all_project_sources"].values():
        assert sha(ROOT / source["path"]) == source["sha256"], source["path"]
    qa = json.loads((ROOT / "verification/WISHART_PAPER_PDF_QA.json").read_text(encoding="utf-8"))
    assert qa["status"] == "PASS" and qa["pdf_sha256"] == sha(ROOT / "output/pdf/wishart_formalization.pdf")
    assert qa["manuscript_sha256"] == sha(PAPER / "main.tex")
    assert qa["rendered_and_visually_inspected_pages"] == list(range(1, qa["pages"] + 1))
    output = ROOT / "output/publication"
    output.mkdir(parents=True, exist_ok=True)
    tex_archive = output / "wishart_latex_source.zip"
    with zipfile.ZipFile(tex_archive, "w", zipfile.ZIP_DEFLATED) as archive:
        archive.write(PAPER / "main.tex", "main.tex")
    paths = {ROOT / src["path"] for src in claims["all_project_sources"].values()}
    paths.update(PAPER.iterdir())
    paths.update((ROOT / "verification/publication_checks").rglob("*"))
    paths.update((ROOT / "verification/workflow_evidence/round3").iterdir())
    paths.update(ROOT / p for p in [
        "theory/jin_wishart_formalization/lean-toolchain",
        "theory/jin_wishart_formalization/lakefile.toml",
        "theory/jin_wishart_formalization/lake-manifest.json",
        "experiments/two_row_log_rate_outage.py",
        "experiments/hermitian_coordinate_metric_control.py",
        "verification/WISHART_LOG_RATE_OUTAGE.json",
        "verification/WISHART_HERMITIAN_METRIC_CONTROL.json",
        "verification/WISHART_WORKFLOW_AUDIT.json",
        "verification/WISHART_INDEPENDENT_REVIEW_STATUS.json",
        "verification/WISHART_PUBLICATION_AUDIT_BINDING.json",
        "verification/WISHART_PUBLICATION_REBUILD.json",
        "verification/WISHART_PAPER_PDF_QA.json",
        "verification/rebuild_wishart_sources.py",
        "verification/prepare_wishart_publication.py",
        "verification/check_publication_axioms.py",
        "verification/prepare_wishart_review.py",
        "verification/accept_wishart_publication.py",
        "verification/wishart_workflow_audit.py",
        "verification/package_wishart_publication.py",
        "verification/WISHART_P4_REVIEW_PACKET.md",
        "verification/WISHART_P4_REVIEW_MANIFEST.json",
        "verification/WISHART_P4_REVIEW_RESPONSE_20261016.md",
        "notes/ARXIV_SUBMISSION_REVIEW_20261016.md",
        "notes/WISHART_STATUS.md",
        "output/pdf/wishart_formalization.pdf",
        "AGENTS.md",
    ])
    paths.update((ROOT / "tools/deepseek_prover").glob("*.py"))
    paths = {p for p in paths if p.is_file()}
    archive_path = output / "wishart_review_artifact.zip"
    with zipfile.ZipFile(archive_path, "w", zipfile.ZIP_DEFLATED) as archive:
        for path in sorted(paths):
            archive.write(path, path.relative_to(ROOT).as_posix())
        archive.writestr("SHA256SUMS.json", json.dumps(
            {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(paths)}, indent=2) + "\n")
    manifest_path = ROOT / "verification/WISHART_P4_REVIEW_MANIFEST.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert manifest["manuscript"]["sha256"] == sha(PAPER / "main.tex")
    review_paths = {ROOT / p["path"] for p in manifest["sources"].values()}
    for p in manifest["sources"].values():
        assert sha(ROOT / p["path"]) == p["sha256"]
    review_paths.update([manifest_path, ROOT / "verification/WISHART_P4_REVIEW_PACKET.md",
                         ROOT / "verification/WISHART_P4_REVIEW_RESPONSE_20261016.md",
                         ROOT / "verification/WISHART_INDEPENDENT_REVIEW_STATUS.json",
                         PAPER / "STEP_REVIEW_DISPOSITION.md",
                         ROOT / "AGENTS.md", PAPER / "main.tex", PAPER / "claims.json",
                         PAPER / "REVISION_STATUS.md"])
    review_archive = output / "wishart_independent_review.zip"
    with zipfile.ZipFile(review_archive, "w", zipfile.ZIP_DEFLATED) as archive:
        for p in sorted(review_paths):
            archive.write(p, p.relative_to(ROOT).as_posix())
        archive.writestr("SHA256SUMS.json", json.dumps(
            {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(review_paths)}, indent=2) + "\n")
    for p in [archive_path, review_archive]:
        with zipfile.ZipFile(p) as archive:
            assert archive.testzip() is None
            for name, digest in json.loads(archive.read("SHA256SUMS.json")).items():
                assert hashlib.sha256(archive.read(name)).hexdigest() == digest, name
    result = {"prepared_for_date": "2026-10-16", "status": "LOCAL_REVIEW_PACKAGE_NOT_SUBMITTED",
              "manuscript": {"path": "theory/wishart_paper/main.tex", "sha256": sha(PAPER / "main.tex")},
              "pdf": {"path": "output/pdf/wishart_formalization.pdf", "sha256": sha(ROOT / "output/pdf/wishart_formalization.pdf")},
              "audit_binding": {"path": "verification/WISHART_PUBLICATION_AUDIT_BINDING.json",
                                "sha256": sha(ROOT / "verification/WISHART_PUBLICATION_AUDIT_BINDING.json")},
              "archives": [{"path": p.relative_to(ROOT).as_posix(), "sha256": sha(p)}
                           for p in [tex_archive, archive_path, review_archive]],
              "archive_byte_integrity": "PASS: every payload hash checked after reopening ZIP",
              "author": "ZHOU XINGYUAN",
              "release_blockers": ["Human mathematical signoff", "Human-selected release license",
                                   "Actual public submission/release", "Final novelty/source review"],
              "artifact_files": len(paths)}
    (ROOT / "verification/WISHART_PAPER_DELIVERY.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"Created local LaTeX source archive and review artifact ({len(paths)} files); no upload")


if __name__ == "__main__":
    main()
