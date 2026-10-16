"""Build a source-linked publication claims manifest; no theorem generation.

This audits source identity and prior actual Lean output. It cannot certify
the intended semantics or replace independent review.
"""
from __future__ import annotations

from datetime import datetime, timezone
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "theory/jin_wishart_formalization"
PAPER = ROOT / "theory/wishart_paper"
SESSION = ROOT / ".tools/publication-revision-20261016"

# Claim / mathematical strength / module / exact declaration identifier.
CLAIMS = [
    ("bartlett-law", "actual_probability_law", "TwoRowRandomDirectionLaw", "actualTwoRow_BartlettCoordinates_law"),
    ("bartlett-density", "actual_density", "TwoRowActualNormalizedDensity", "actualTwoRow_BartlettRealCoordinates_eq_normalizedDensity"),
    ("gram-density", "actual_density", "TwoRowActualDensity", "actualTwoRow_GramRealCoordinates_eq_traceDensity"),
    ("wishart-density-api", "actual_density_interface", "TwoRowActualNormalizedDensity", "complexWishart_twoRow_realCoordinates_eq_traceDensity"),
    ("frobenius-reference-density", "reference_measure_conversion_of_actual_density", "HermitianCoordinateMetric", "actualTwoRow_Gram_frobeniusFrameDensity"),
    ("minimum-tail", "actual_probability", "TwoRowMinimumLaw", "actualTwoRow_minimum_tail"),
    ("minimum-cdf", "actual_probability", "TwoRowMinimumLaw", "actualTwoRow_minimum_CDF"),
    ("minimum-law", "actual_probability_law", "TwoRowMinimumLaw", "actualTwoRow_minimum_law_expTwo"),
    ("original-central-candidate", "candidate_equals_actual_CDF_special_case", "Theorem1CentralTwoRowActualCDF", "theorem1CentralTwoRow_candidate_eq_actualCDF"),
    ("scaled-law", "actual_probability_law", "TwoRowScaledMinimum", "actualTwoRow_scaled_minimum_law"),
    ("variance-cdf", "actual_probability", "TwoRowScaledMinimum", "actualTwoRow_covariance_minimum_CDF"),
    ("log-rate-event", "deterministic_event", "TwoRowLogRateOutage", "log_one_add_mul_le_iff"),
    ("log-rate-outage", "actual_probability", "TwoRowLogRateOutage", "actualTwoRow_weakestLogRate_outage"),
    ("log-rate-negative", "actual_probability", "TwoRowLogRateOutage", "actualTwoRow_weakestLogRate_outage_negative"),
    ("fixed-projection", "actual_probability_law_fixed_subspace", "GaussianOrthogonalProjectionLaw", "stdGaussian_orthogonalProjectionOnto_law"),
    ("projected-energy", "actual_probability_law_fixed_subspace", "GaussianOrthogonalProjectionLaw", "stdGaussian_projected_half_norm_sq_law"),
    ("fixed-split", "actual_probability_law_fixed_subspace", "GaussianOrthogonalSplitLaw", "stdGaussian_orthogonal_split_law"),
    ("noncentral-one-column-asymptotic", "actual_CDF_limit", "T4NoncentralOneColumnAnyRows", "noncentralOneColumnSmallestCDF_div_tendsto_frobenius"),
    ("two-row-one-column", "candidate_equals_actual_CDF_special_case", "Theorem1TwoRowsActualCDF", "theorem1TwoRowsCandidate_eq_actualCDF"),
    ("three-row-one-column", "candidate_equals_actual_CDF_special_case", "Theorem1ThreeRowsActualCDF", "theorem1ThreeRowsOneColumnCandidate_eq_actualCDF"),
    ("generic-cone-integral", "candidate_integral_NOT_actual_general_probability", "CentralWishartConeIntegral", "centralCone_candidateIntegral_shift"),
    ("hermitian-coordinate-volume", "coordinate_interface", "CentralHermitianCoordinates", "hermitianRealCoordinateEquiv_measurePreserving"),
]

LOCAL_HELPERS = [
    ("DeepSeekScale20261015.SampleMatrix", "JinWishart.deepseek_scaled_sampleMatrix"),
    ("DeepSeekMinimumCDF20261013.DeterminantFactor", "deepseek_minimum_DeterminantFactor"),
    ("DeepSeekCollaborationRound320261011.ComplexScaledCoefficient", "deepseek_round3_ComplexScaledCoefficient"),
    ("DeepSeekCollaborationRound320261011.ComplexScaledNormSquare", "deepseek_round3_ComplexScaledNormSquare"),
]


def code_only(source: str) -> str:
    """Remove nested block comments, line comments and quoted strings."""
    output, i, depth = [], 0, 0
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                output.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            output.append(" ")
        else:
            output.append(source[i])
            i += 1
    if depth:
        raise ValueError("Unclosed Lean comment")
    return "".join(output)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def scan_sources():
    sources, code, dependencies = {}, {}, {}
    for path in list((PROJECT / "JinWishartFormalization").rglob("*.lean")) + [PROJECT / "JinWishartFormalization.lean"]:
        name = path.relative_to(PROJECT).with_suffix("").as_posix().replace("/", ".")
        text = path.read_text(encoding="utf-8", errors="strict")
        assert "\ufffd" not in text
        code[name] = code_only(text)
        forbidden = re.findall(r"\b(?:sorry|admit|axiom|native_decide)\b", code[name])
        assert not forbidden, (name, forbidden)
        sources[name] = {"path": path.relative_to(ROOT).as_posix(), "sha256": sha(path)}
        dependencies[name] = re.findall(r"^import\s+(\S+)", code[name], re.M)
    return sources, code, dependencies


def audit_targets(code):
    targets = {}
    for short in sorted({item[2] for item in CLAIMS}):
        module = "JinWishartFormalization." + short
        for name in re.findall(r"^(?:theorem|lemma)\s+(\w+)", code[module], re.M):
            targets["JinWishart." + name] = {"module": module, "coverage": "all public theorems in named entry module"}
    for short, name in LOCAL_HELPERS:
        targets[name] = {"module": "JinWishartFormalization." + short, "coverage": "explicit local helper in headline chain"}
    return dict(sorted(targets.items()))


def generate_audit_source(code):
    targets = audit_targets(code)
    path = PAPER / "ClaimsCheck.lean"
    content = "import JinWishartFormalization\n\n-- Generated expanded publication axiom audit; no new theorem.\n"
    content += "\n".join("#print axioms " + name for name in targets) + "\n"
    if not path.exists() or path.read_text(encoding="utf-8") != content:
        path.write_text(content, encoding="utf-8")
    return path, targets


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generate-only", action="store_true")
    args = parser.parse_args()
    sources, code, dependencies = scan_sources()
    claims_check, targets = generate_audit_source(code)
    if args.generate_only:
        print(f"Generated audit of {len(targets)} public declarations; no kernel success claimed")
        return
    rebuild_path = ROOT / "verification/WISHART_PUBLICATION_REBUILD.json"
    rebuild = json.loads(rebuild_path.read_text(encoding="utf-8"))
    assert rebuild["status"] == "PASS"
    records = {r["module"]: r for r in rebuild["records"]}
    for name in sources:
        record = records.get(name)
        assert record and record["exit_code"] == 0 and record["source_unchanged"]
        assert record["sha256"] == sources[name]["sha256"], (name, "stale source")
    entries = []
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    claims_log_path = ROOT / "verification/publication_checks/claims-axioms.txt"
    claims_log = claims_log_path.read_text(encoding="utf-8")
    binding_path = ROOT / "verification/WISHART_PUBLICATION_AUDIT_BINDING.json"
    binding = json.loads(binding_path.read_text(encoding="utf-8"))
    assert binding["status"] == "PASS"
    assert binding["audit_source"]["sha256"] == sha(claims_check)
    assert binding["audit_log"]["sha256"] == sha(claims_log_path)
    assert binding["manuscript"]["sha256"] == sha(PAPER / "main.tex")
    assert binding["project_source_snapshot"] == sources
    assert set(binding["targets"]) == set(targets)
    for name, item in targets.items():
        match = re.search(re.escape("'" + name + "' depends on axioms:") + r"\s*\[([^\]]*)\]", claims_log)
        empty = "'" + name + "' does not depend on any axioms" in claims_log
        assert match or empty, (name, "not printed")
        axioms = {x.strip() for x in match[1].split(",") if x.strip()} if match else set()
        assert axioms <= allowed, (name, axioms)
    for claim, strength, short_module, declaration in CLAIMS:
        module = "JinWishartFormalization." + short_module
        assert re.search(r"\b(?:theorem|lemma)\s+" + re.escape(declaration) + r"\b", code[module]), declaration
        session = ROOT / rebuild["session"]
        log = (session / (module + ".txt")).read_text(encoding="utf-8")
        name = "JinWishart." + declaration
        match = re.search(re.escape("'" + name + "' depends on axioms:") + r"\s*\[([^\]]*)\]", log)
        axioms = [x.strip() for x in match[1].split(",") if x.strip()] if match else None
        if axioms is not None:
            assert set(axioms) <= allowed, (name, axioms)
        unified = re.search(re.escape("'" + name + "' depends on axioms:") + r"\s*\[([^\]]*)\]", claims_log)
        audited_axioms = [x.strip() for x in unified[1].split(",") if x.strip()] if unified else None
        if audited_axioms is not None:
            assert set(audited_axioms) <= allowed, (name, audited_axioms)
        closure = set()

        def visit(current):
            if current in closure:
                return
            closure.add(current)
            for dep in dependencies[current]:
                if dep in sources:
                    visit(dep)

        visit(module)
        entries.append({"claim": claim, "strength": strength, "declaration": name,
                        "module": module, "source": sources[module],
                        "fresh_source_check": "PASS", "axioms_printed_in_module_log": axioms,
                        "axioms_in_publication_claims_audit": audited_axioms,
                        "project_dependency_modules": sorted(closure),
                        "immediate_proof_body_origin": "Codex",
                        "guided_local_helpers_in_dependencies": [n for m, n in LOCAL_HELPERS
                            if "JinWishartFormalization." + m in closure],
                        "transitive_local_prover_modules": sorted(m for m in closure if ".DeepSeek" in m),
                        "semantic_review": "PENDING [需人工审查]"})
    numerical = ROOT / "verification/WISHART_LOG_RATE_OUTAGE.json"
    data = {"prepared_for_date": "2026-10-16", "generated_utc": datetime.now(timezone.utc).isoformat(),
            "toolchain": rebuild["toolchain"], "mathlib_revision": "e18afff334217588afc719a8b707b00d90521064",
            "status": "SOURCE_CHECKED_MANUSCRIPT; author ZHOU XINGYUAN; human semantic signoff pending",
            "fresh_source_rebuild": {"status": rebuild["status"], "modules": len(sources),
                                     "report": "verification/WISHART_PUBLICATION_REBUILD.json",
                                     "report_sha256": sha(ROOT / "verification/WISHART_PUBLICATION_REBUILD.json"),
                                     "full_Lake_build": "NOT_RUN", "external_package_caches": True},
            "lexical_source_audit": {"UTF8": "PASS", "forbidden_code_tokens": [], "comments_and_strings_excluded": True},
            "claims_audit": {"source": claims_check.relative_to(ROOT).as_posix(), "source_sha256": sha(claims_check),
                             "log": claims_log_path.relative_to(ROOT).as_posix(),
                             "log_sha256": sha(claims_log_path) if claims_log_path.exists() else None,
                             "public_declaration_count": len(targets), "all_targets_printed_standard_axioms": True,
                             "binding": binding_path.relative_to(ROOT).as_posix(), "binding_sha256": sha(binding_path),
                             "coverage": targets},
            "numerical_control": {"path": numerical.relative_to(ROOT).as_posix(), "sha256": sha(numerical)},
            "claims": entries, "all_project_sources": sources}
    (PAPER / "claims.json").write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    evidence = ROOT / "verification/publication_checks"
    evidence.mkdir(exist_ok=True)
    for filename in ["JinWishartFormalization.txt", "JinWishartFormalization.FourRowSampleCoordinates.txt"]:
        shutil.copy2(session / filename, evidence / filename)
    print(f"PASS: {len(entries)} mapped claims; {len(sources)} matching fresh-source checks; UTF8/token audit")


if __name__ == "__main__":
    main()
