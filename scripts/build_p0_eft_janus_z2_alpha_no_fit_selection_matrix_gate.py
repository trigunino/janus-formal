from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_z2_alpha_no_fit_selection_matrix_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_alpha_no_fit_selection_matrix_gate.md"


ROUTES: list[dict[str, Any]] = [
    {
        "id": 1,
        "route": "global_action_energy_principle",
        "status": "open",
        "hard_blocker": "finite_on_shell_bimetric_action_for_noncompact_exact_orbit",
        "no_fit_if_closed": True,
    },
    {
        "id": 2,
        "route": "PT_Souriau_quantization",
        "status": "blocked",
        "hard_blocker": "nonzero_KKS_density_or_compact_PT_cycle_missing",
        "no_fit_if_closed": True,
    },
    {
        "id": 3,
        "route": "horizon_null_thermodynamics",
        "status": "open",
        "hard_blocker": "null_PT_boundary_action_temperature_entropy_law_missing",
        "no_fit_if_closed": True,
    },
    {
        "id": 4,
        "route": "LL_brane_bridge_state",
        "status": "conditional",
        "hard_blocker": "chi_LL_selection_law_missing",
        "no_fit_if_closed": True,
    },
    {
        "id": 5,
        "route": "spinor_torsion_Nieh_Yan",
        "status": "archived_for_active_PT67",
        "hard_blocker": "no_active_torsion_source_on_Sigma",
        "no_fit_if_closed": True,
    },
    {
        "id": 6,
        "route": "topological_flux_area_gap",
        "status": "blocked",
        "hard_blocker": "flux_unit_and_primitive_sector_missing",
        "no_fit_if_closed": True,
    },
    {
        "id": 7,
        "route": "bimetric_vacuum_equation_of_state",
        "status": "open",
        "hard_blocker": "absolute_density_normalization_missing",
        "no_fit_if_closed": True,
    },
    {
        "id": 8,
        "route": "boundary_reference_Brown_York",
        "status": "mostly_exhausted",
        "hard_blocker": "active_PT67_regular_projection_zero",
        "no_fit_if_closed": True,
    },
    {
        "id": 9,
        "route": "observational_sector_selection",
        "status": "viable_not_no_fit",
        "hard_blocker": "requires_SN_BAO_Hz_calibration",
        "no_fit_if_closed": False,
    },
    {
        "id": 10,
        "route": "alternative_tunnel_geometry",
        "status": "open",
        "hard_blocker": "must_be_lifted_from_Janus_not_added_ad_hoc",
        "no_fit_if_closed": None,
    },
    {
        "id": 11,
        "route": "Moebius_twisted_throat_geometry",
        "status": "new_candidate",
        "hard_blocker": "needs_4D_lift_compact_cycle_and_nonzero_theta_period",
        "no_fit_if_closed": None,
    },
    {
        "id": 12,
        "route": "quantum_state_superselection_law",
        "status": "blocked",
        "hard_blocker": "primitive_sector_irreducibility_missing",
        "no_fit_if_closed": True,
    },
]


def build_payload() -> dict[str, Any]:
    open_or_new = [r for r in ROUTES if r["status"] in {"open", "new_candidate", "conditional"}]
    no_fit_routes = [r for r in ROUTES if r["no_fit_if_closed"] is True]
    return {
        "status": "janus-z2-alpha-no-fit-selection-matrix-gate",
        "active_core": "Z2_tunnel_Sigma",
        "baseline": "alpha_is_continuous_global_energy_state_sector",
        "route_count": len(ROUTES),
        "routes": ROUTES,
        "open_or_conditional_route_ids": [r["id"] for r in open_or_new],
        "potential_no_fit_route_ids": [r["id"] for r in no_fit_routes],
        "recommended_order": [1, 3, 11, 2, 7, 9],
        "moebius_verdict": (
            "Moebius/twisted geometry can supply orientation reversal and a compact "
            "cycle candidate, but not alpha unless lifted to the 4D Janus tunnel "
            "with a nonzero boundary symplectic/theta period."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Alpha No-Fit Selection Matrix Gate",
        "",
        f"Route count: `{payload['route_count']}`",
        f"Open/conditional route ids: `{payload['open_or_conditional_route_ids']}`",
        f"Potential no-fit route ids: `{payload['potential_no_fit_route_ids']}`",
        f"Recommended order: `{payload['recommended_order']}`",
        "",
        payload["moebius_verdict"],
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
