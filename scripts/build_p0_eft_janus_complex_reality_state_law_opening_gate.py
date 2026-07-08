from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_state_law_opening_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_state_law_opening_gate.md"
PLAN_PATH = Path("docs/janus_complex_reality_state_law_plan.md")


def build_payload() -> dict[str, Any]:
    objectives = [
        "curate_complex_reality_formula_anchors",
        "define_complex_coadjoint_state_space",
        "identify_janus_pt_real_slice_for_mass_and_alpha",
        "derive_or_reject_nonzero_kks_boundary_density",
        "test_prequantization_integrality",
        "map_quantized_charge_to_alpha_if_available",
        "emit_alpha_state_law_verdict",
    ]
    blockers = [
        "nonzero_KKS_or_boundary_symplectic_density_not_yet_derived",
        "integrality_periods_not_yet_computed",
        "mass_or_charge_lattice_not_yet_derived",
        "primitive_sector_law_not_yet_derived",
    ]
    return {
        "status": "janus-complex-reality-state-law-opening-gate",
        "conceptual_branch": "janus_complex_reality_state_law",
        "branch_opened": True,
        "source_anchor": "X2026-complex-reality",
        "source_role": "fundamental_state_law_candidate_not_observational_contract",
        "plan_path": str(PLAN_PATH),
        "target_problem": "alpha_global_state_selection",
        "allowed_source_family": [
            "complex_Poincare_group",
            "complex_coadjoint_action",
            "Souriau_moment_map",
            "geometric_quantization_hints",
            "Janus_PT_mass_sign_pairing",
        ],
        "forbidden_claims": [
            "alpha_fixed_now",
            "SN_BAO_CMB_matched_now",
            "full_FLRW_background_emitted_now",
            "paper_2024_frontier_unfrozen",
        ],
        "objectives": objectives,
        "current_blockers": blockers,
        "alpha_generated_now": False,
        "observational_branch_opened": False,
        "first_plan_ready": PLAN_PATH.exists(),
        "next_gate": "ComplexRealitySourceFormulaCurationGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality State Law Opening Gate",
                "",
                f"Branch opened: `{payload['branch_opened']}`",
                f"Conceptual branch: `{payload['conceptual_branch']}`",
                f"Source anchor: `{payload['source_anchor']}`",
                f"Target problem: `{payload['target_problem']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                f"Next gate: `{payload['next_gate']}`",
                "",
                "## Current Blockers",
                "",
                *[f"- `{item}`" for item in payload["current_blockers"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
