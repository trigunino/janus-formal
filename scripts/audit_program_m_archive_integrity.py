"""MF-ARC-001: integrity checks for the current Program M archive."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
RECORDS = {
    "MF-ARC-001": ("docs/program_m_archive.md", "scripts/audit_program_m_archive_integrity.py", "outputs/program_m/mf_arc_001_archive_integrity.json", "tests/test_program_m_archive_integrity.py"),
    "MF-AX-001": ("docs/program_m_axiom_boundary.md", "scripts/audit_program_m_axiom_boundary.py", "outputs/program_m/mf_ax_001_axiom_boundary.json", "tests/test_program_m_axiom_boundary.py"),
    "MF-SEP-001": ("docs/program_m_recursive_separator_locality.md", "scripts/audit_program_m_recursive_separator_locality.py", "outputs/program_m/mf_sep_001_recursive_separator_locality.json", "tests/test_program_m_recursive_separator_locality.py"),
    "MF-SEP-002": ("docs/program_m_separator_target_compatibility.md", "scripts/audit_program_m_separator_target_compatibility.py", "outputs/program_m/mf_sep_002_separator_target_compatibility.json", "tests/test_program_m_separator_target_compatibility.py"),
    "MF-SEL-002": ("docs/program_m_selection_from_axioms_nogo.md", "scripts/audit_program_m_selection_from_axioms_nogo.py", "outputs/program_m/mf_sel_002_selection_from_axioms_nogo.json", "tests/test_program_m_selection_from_axioms_nogo.py"),
    "MF-PBRIDGE-001": ("docs/program_m_program_p_bridge.md", "scripts/audit_program_m_program_p_bridge.py", "outputs/program_m/mf_pbridge_001_program_p_bridge.json", "tests/test_program_m_program_p_bridge.py"),
    "MF-CONF-001": ("docs/program_m_configuration_groupoid.md", "scripts/audit_program_m_configuration_groupoid.py", "outputs/program_m/mf_conf_001_configuration_groupoid.json", "tests/test_program_m_configuration_groupoid.py"),
    "MF-OBS-001": ("docs/program_m_configuration_observables.md", "scripts/audit_program_m_configuration_observables.py", "outputs/program_m/mf_obs_001_configuration_observables.json", "tests/test_program_m_configuration_observables.py"),
    "MF-COMP-002": ("docs/program_m_configuration_composition.md", "scripts/audit_program_m_configuration_composition.py", "outputs/program_m/mf_comp_002_configuration_composition.json", "tests/test_program_m_configuration_composition.py"),
    "MF-GLUE-001": ("docs/program_m_interface_gluing.md", "scripts/audit_program_m_interface_gluing.py", "outputs/program_m/mf_glue_001_interface_gluing.json", "tests/test_program_m_interface_gluing.py"),
    "MF-GLUE-002": ("docs/program_m_gluing_coherence.md", "scripts/audit_program_m_gluing_coherence.py", "outputs/program_m/mf_glue_002_gluing_coherence.json", "tests/test_program_m_gluing_coherence.py"),
    "MF-DESC-001": ("docs/program_m_primitive_descent.md", "scripts/audit_program_m_primitive_descent.py", "outputs/program_m/mf_desc_001_primitive_descent.json", "tests/test_program_m_primitive_descent.py"),
    "MF-DESC-002": ("docs/program_m_descent_reachability.md", "scripts/audit_program_m_descent_reachability.py", "outputs/program_m/mf_desc_002_descent_reachability.json", "tests/test_program_m_descent_reachability.py"),
    "MF-FREE-001": ("docs/program_m_free_preorder.md", "scripts/audit_program_m_free_preorder.py", "outputs/program_m/mf_free_001_free_preorder.json", "tests/test_program_m_free_preorder.py"),
    "MF-GEO-001": ("docs/program_m_geometry_bifurcation.md", "scripts/audit_program_m_geometry_bifurcation.py", "outputs/program_m/mf_geo_001_geometry_bifurcation.json", "tests/test_program_m_geometry_bifurcation.py"),
    "MF-GEO-002": ("docs/program_m_geometric_gluing_selection.md", "scripts/audit_program_m_geometric_gluing_selection.py", "outputs/program_m/mf_geo_002_geometric_gluing_selection.json", "tests/test_program_m_geometric_gluing_selection.py"),
    "MF-REF-001": ("docs/program_m_pairwise_refinement.md", "scripts/audit_program_m_pairwise_refinement.py", "outputs/program_m/mf_ref_001_pairwise_refinement.json", "tests/test_program_m_pairwise_refinement.py"),
    "MF-DIST-001": ("docs/program_m_free_directed_distance.md", "scripts/audit_program_m_free_directed_distance.py", "outputs/program_m/mf_dist_001_free_directed_distance.json", "tests/test_program_m_free_directed_distance.py"),
    "MF-WEIGHT-001": ("docs/program_m_weight_selection_nogo.md", "scripts/audit_program_m_weight_selection_nogo.py", "outputs/program_m/mf_weight_001_weight_selection_nogo.json", "tests/test_program_m_weight_selection_nogo.py"),
    "MF-MEAS-001": ("docs/program_m_measure_extension.md", "scripts/audit_program_m_measure_extension.py", "outputs/program_m/mf_meas_001_measure_extension.json", "tests/test_program_m_measure_extension.py"),
    "MF-SIGN-001": ("docs/program_m_signed_involution.md", "scripts/audit_program_m_signed_involution.py", "outputs/program_m/mf_sign_001_signed_involution.json", "tests/test_program_m_signed_involution.py"),
    "MF-INV-001": ("docs/program_m_canonical_involution.md", "scripts/audit_program_m_canonical_involution.py", "outputs/program_m/mf_inv_001_canonical_involution.json", "tests/test_program_m_canonical_involution.py"),
    "MF-INV-002": ("docs/program_m_involution_composition.md", "scripts/audit_program_m_involution_composition.py", "outputs/program_m/mf_inv_002_involution_composition.json", "tests/test_program_m_involution_composition.py"),
    "MF-INV-003": ("docs/program_m_equivariant_gluing.md", "scripts/audit_program_m_equivariant_gluing.py", "outputs/program_m/mf_inv_003_equivariant_gluing.json", "tests/test_program_m_equivariant_gluing.py"),
    "MF-PBRIDGE-002": ("docs/program_m_signed_program_p_adapter.md", "scripts/audit_program_m_signed_program_p_adapter.py", "outputs/program_m/mf_pbridge_002_signed_program_p_adapter.json", "tests/test_program_m_signed_program_p_adapter.py"),
    "MF-DIM-001B": ("docs/program_m_multirank_dimension.md", "scripts/audit_program_m_multirank_dimension.py", "outputs/program_m/mf_dim_001_multirank_dimension.json", "tests/test_program_m_multirank_dimension.py"),
    "MF-DIM-002": ("docs/program_m_high_rank_dimension.md", "scripts/audit_program_m_high_rank_dimension.py", "outputs/program_m/mf_dim_002_high_rank_dimension.json", "tests/test_program_m_high_rank_dimension.py"),
    "MF-DIM-003": ("docs/program_m_no_finite_dimension_cutoff.md", "scripts/audit_program_m_no_finite_dimension_cutoff.py", "outputs/program_m/mf_dim_003_no_finite_dimension_cutoff.json", "tests/test_program_m_no_finite_dimension_cutoff.py"),
    "MF-KER-001": ("docs/program_m_weak_kernel_axioms.md", "scripts/audit_program_m_weak_kernel_axioms.py", "outputs/program_m/mf_ker_001_weak_kernel_axioms.json", "tests/test_program_m_weak_kernel_axioms.py"),
    "MF-KER-002": ("docs/program_m_candidate_kernel_axioms.md", "scripts/audit_program_m_candidate_kernel_axioms.py", "outputs/program_m/mf_ker_002_candidate_kernel_axioms.json", "tests/test_program_m_candidate_kernel_axioms.py"),
}


def run_audit() -> dict[str, object]:
    register = (ROOT / "docs/program_m_provenance_register.md").read_text(encoding="utf-8")
    identifiers = re.findall(r"^\| `([^`]+)` \|", register, flags=re.MULTILINE)
    duplicates = sorted(key for key, count in Counter(identifiers).items() if count > 1)
    rows = []
    for identifier, paths in RECORDS.items():
        missing = [path for path in paths if not (ROOT / path).is_file()]
        rows.append({"id": identifier, "artifacts": list(paths), "missing": missing})
    return {
        "program": "MF-ARC-001",
        "records": rows,
        "duplicate_provenance_ids": duplicates,
        "gates": {
            "provenance_ids_are_unique": not duplicates,
            "recent_records_have_complete_artifacts": all(not row["missing"] for row in rows),
            "archive_index_exists": (ROOT / "docs/program_m_archive.md").is_file(),
            "current_status_note_exists": (ROOT / "docs/program_m_status.md").is_file(),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(run_audit(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
