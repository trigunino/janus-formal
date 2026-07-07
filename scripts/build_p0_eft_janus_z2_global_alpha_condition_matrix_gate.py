from __future__ import annotations

import json
from pathlib import Path
from typing import Any


JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_global_alpha_condition_matrix_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_global_alpha_condition_matrix_gate.md")


def build_payload() -> dict[str, Any]:
    candidates = [
        {
            "id": "projective_closure",
            "janus_motivation": "S4/P4 projective cover and resolved tunnel make a global return map natural.",
            "derived_assets": ["two_fold_cover", "aroundSigma_Z2_cycle"],
            "missing_assets": ["canonical phase variable", "action period I(alpha)"],
            "can_quantize_alpha": False,
            "rustine_risk": "medium",
            "verdict": "coherent_geometry_not_selector",
        },
        {
            "id": "PT_monodromy_identity",
            "janus_motivation": "PT transport through the bridge should return physical states up to allowed sheet flip.",
            "derived_assets": ["PT_transport", "Z2_sheet_cycle"],
            "missing_assets": ["nontrivial quantum phase/holonomy", "I(alpha)/hbar phase map"],
            "can_quantize_alpha": False,
            "rustine_risk": "medium_low_if_phase_is_derived",
            "verdict": "best_candidate_if_holonomy_phase_derived",
        },
        {
            "id": "bridge_regular_vacuum",
            "janus_motivation": "resolved Big Bang/Big Crunch tunnel should be defect-free and stable.",
            "derived_assets": ["regular_PT67_zero_charge_branch"],
            "missing_assets": ["nonzero vacuum energy functional", "unique minimum"],
            "can_quantize_alpha": False,
            "rustine_risk": "medium",
            "verdict": "currently_selects_zero_or_scale_invariant_branch",
        },
        {
            "id": "global_plus_minus_neutrality",
            "janus_motivation": "positive and negative sectors suggest total signed balance.",
            "derived_assets": ["published_sector_ratio"],
            "missing_assets": ["absolute charge scale", "bridge residual charge law"],
            "can_quantize_alpha": False,
            "rustine_risk": "medium_high",
            "verdict": "balance_constraint_not_scale_selector",
        },
        {
            "id": "primitive_nontrivial_sector",
            "janus_motivation": "the universe could occupy the minimal nonzero throat/charge sector.",
            "derived_assets": ["integer_sector_logic"],
            "missing_assets": ["charge lattice unit", "irreducibility theorem"],
            "can_quantize_alpha": False,
            "rustine_risk": "medium",
            "verdict": "needs_lattice_before_n_equals_one_matters",
        },
        {
            "id": "janus_vacuum_minimum",
            "janus_motivation": "alpha might be the minimum of a global bimetric vacuum energy.",
            "derived_assets": ["alpha_Eglobal_relation"],
            "missing_assets": ["global vacuum functional V(alpha)", "positive stability criterion"],
            "can_quantize_alpha": False,
            "rustine_risk": "low_if_V_is_action_derived",
            "verdict": "most_physical_continuous_selector_if_derived",
        },
    ]
    return {
        "status": "janus-z2-global-alpha-condition-matrix-gate",
        "active_core": "Z2_tunnel_Sigma",
        "candidates": candidates,
        "best_discrete_route": "PT_monodromy_identity",
        "best_continuous_route": "janus_vacuum_minimum",
        "current_strongest_safe_statement": (
            "Projective/tunnel topology gives a Z2 global cycle, but not a "
            "quantum phase. The least artificial discrete route is PT monodromy "
            "only if the holonomy phase is derived from the boundary/symplectic "
            "form. The least artificial continuous route is a bimetric vacuum "
            "functional V(alpha) derived from the action."
        ),
        "alpha_generated_now": False,
        "next_non_rustine_tests": [
            "derive PT holonomy phase from existing boundary theta or KKS density",
            "derive V(alpha) by evaluating the published bimetric minisuperspace action on the exact solution",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Global Alpha Condition Matrix Gate",
                "",
                f"Best discrete route: `{payload['best_discrete_route']}`",
                f"Best continuous route: `{payload['best_continuous_route']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                "",
                payload["current_strongest_safe_statement"],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
