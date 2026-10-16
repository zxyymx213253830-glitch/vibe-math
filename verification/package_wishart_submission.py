"""Package submission code and an arXiv anc layout without publishing."""
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path
import zipfile

from prepare_wishart_publication import ROOT, PAPER, scan_sources, sha


def write_zip(path, payload):
    with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as archive:
        for name, data in sorted(payload.items()):
            assert not name.startswith("/") and ".." not in Path(name).parts
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 16, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, data)
    with zipfile.ZipFile(path) as archive:
        assert archive.testzip() is None
        for name, data in payload.items():
            assert archive.read(name) == data


def main():
    sources, _, deps = scan_sources()
    claims = json.loads((PAPER / "claims.json").read_text(encoding="utf-8"))
    assert sources == claims["all_project_sources"]
    binding = json.loads((ROOT / "verification/WISHART_PUBLICATION_AUDIT_BINDING.json").read_text(encoding="utf-8"))
    assert binding["status"] == "PASS" and binding["manuscript"]["sha256"] == sha(PAPER / "main.tex")
    for imports in deps.values():
        assert all(not name.startswith("JinWishartFormalization") or name in sources for name in imports)
    paths = {ROOT / s["path"] for s in sources.values()}
    required = [
        "AGENTS.md",
        "theory/jin_wishart_formalization/lean-toolchain",
        "theory/jin_wishart_formalization/lakefile.toml",
        "theory/jin_wishart_formalization/lake-manifest.json",
        "theory/wishart_paper/ClaimsCheck.lean",
        "theory/wishart_paper/claims.json", "theory/wishart_paper/REPRODUCIBILITY.md",
        "theory/wishart_paper/RESULTS.md", "theory/wishart_paper/REVISION_STATUS.md",
        "theory/wishart_paper/SUBMISSION_CODE_SUMMARY.md",
        "theory/wishart_paper/STEP_REVIEW_DISPOSITION.md",
        "verification/WISHART_P4_REVIEW_RESPONSE_20261016.md",
        "verification/WISHART_P4_REVIEW_MANIFEST.json",
        "verification/WISHART_INDEPENDENT_REVIEW_STATUS.json",
        "notes/ARXIV_SUBMISSION_REVIEW_20261016.md",
        "verification/WISHART_PUBLICATION_REBUILD.json",
        "verification/WISHART_PUBLICATION_AUDIT_BINDING.json",
        "verification/WISHART_PAPER_PDF_QA.json", "verification/WISHART_WORKFLOW_AUDIT.json",
        "verification/WISHART_LOG_RATE_OUTAGE.json", "verification/WISHART_HERMITIAN_METRIC_CONTROL.json",
        "verification/publication_checks/claims-axioms.txt",
        "experiments/two_row_log_rate_outage.py", "experiments/hermitian_coordinate_metric_control.py",
        "verification/rebuild_wishart_sources.py", "verification/check_publication_axioms.py",
        "verification/prepare_wishart_publication.py", "verification/wishart_workflow_audit.py",
        "verification/prepare_wishart_review.py", "verification/accept_wishart_publication.py",
        "verification/package_wishart_submission.py",
        "tools/deepseek_prover/collaborative_check.py", "tools/deepseek_prover/hour_runner.py",
        "tools/deepseek_prover/prove.py",
    ]
    paths.update(ROOT / p for p in required)
    paths.update((ROOT / "verification/workflow_evidence/round3").iterdir())
    # Include actual core compilation evidence, not model billing/credential logs.
    paths.update((ROOT / "verification/publication_checks/revision-20261016").glob("*.txt"))
    paths.add(ROOT / "verification/publication_checks/JinWishartFormalization.txt")
    paths.add(ROOT / "verification/publication_checks/acceptance-20261016/metric-3.txt")
    paths.update(p for p in (ROOT / "verification/publication_checks/step-review-20261016").iterdir()
                 if p.suffix != ".tex")
    assert all(p.suffix != ".tex" for p in paths), "Ancillary code archive must not contain TeX sources"
    payload = {p.relative_to(ROOT).as_posix(): p.read_bytes() for p in sorted(paths)}
    payload["README_SUBMISSION.md"] = (PAPER / "SUBMISSION_CODE_SUMMARY.md").read_bytes()
    checksums = {name: hashlib.sha256(data).hexdigest() for name, data in payload.items()}
    payload["SOURCE_MANIFEST.json"] = (json.dumps(checksums, indent=2) + "\n").encode()
    output = ROOT / "output/publication"
    output.mkdir(exist_ok=True)
    code = output / "wishart_formalization_code.zip"
    write_zip(code, payload)
    with zipfile.ZipFile(code) as archive:
        for name, digest in json.loads(archive.read("SOURCE_MANIFEST.json")).items():
            assert hashlib.sha256(archive.read(name)).hexdigest() == digest
    readme = ("Lean source and evidence accompany main.tex. "
              "The code ZIP preserves the original repository paths. TeX is only at the submission root.\n"
              f"Code ZIP SHA256: {sha(code)}\n"
              "Author: ZHOU XINGYUAN. This local package is not submitted. Release rights/license "
              "and human mathematical signoff remain the author's responsibility.\n")
    upload = output / "wishart_arxiv_upload.zip"
    write_zip(upload, {"main.tex": (PAPER / "main.tex").read_bytes(),
                       "anc/wishart_formalization_code.zip": code.read_bytes(),
                       "anc/README.txt": readme.encode()})
    with zipfile.ZipFile(upload) as outer:
        with zipfile.ZipFile(io.BytesIO(outer.read("anc/wishart_formalization_code.zip"))) as inner:
            assert inner.testzip() is None
            assert len([p for p in inner.namelist() if p.endswith(".lean")]) == len(sources) + 1
    result = {"created_utc": datetime.now(timezone.utc).isoformat(),
              "status": "LOCAL_PACKAGED_NOT_SUBMITTED", "author": "ZHOU XINGYUAN", "project_modules": len(sources),
              "manuscript_sha256": sha(PAPER / "main.tex"),
              "pdf_sha256": sha(ROOT / "output/pdf/wishart_formalization.pdf"),
              "existing_Step_report_sha256": sha(ROOT / "verification/WISHART_P4_REVIEW_RESPONSE_20261016.md"),
              "audit_declarations": claims["claims_audit"]["public_declaration_count"],
              "mapped_claims": len(claims["claims"]), "source_payload_files": len(checksums),
              "byte_integrity": "PASS; all payloads and nested archive reopened and checked",
              "project_import_closure": "PASS", "license": "NOT_SELECTED_BY_ASSISTANT",
              "excluded": [".lake", ".tools", "model weights", "application settings", "credentials", "scratch files"],
              "archives": [{"path": p.relative_to(ROOT).as_posix(), "sha256": sha(p), "bytes": p.stat().st_size}
                           for p in [code, upload]],
              "upload_roots": ["main.tex", "anc/wishart_formalization_code.zip", "anc/README.txt"]}
    (ROOT / "verification/WISHART_SUBMISSION_PACKAGE.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"Packaged {len(sources)} project modules; {len(checksums)} verified payload files; no publication")


if __name__ == "__main__":
    main()
