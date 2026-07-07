from __future__ import annotations

import json
from pathlib import Path
from typing import Any


JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_alpha_solution_search_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_alpha_solution_search_gate.md")


ROUTES: list[dict[str, Any]] = [
    {
        "id": "exact_solution_integration_constant_state_sector",
        "kind": "classical_state_sector",
        "status": "usable_conditional_solution",
        "fixes_alpha": True,
        "full_no_fit": False,
        "needs": ["alpha_m as global solution-sector datum"],
        "meaning": "alpha is the dimensional integration constant of the exact Janus solution, analogous to ADM/Schwarzschild mass.",
        "bibliography": ["Janus exact solution pages already indexed locally"],
    },
    {
        "id": "brown_york_or_wald_boundary_charge",
        "kind": "boundary_charge",
        "status": "equivalent_if_charge_available",
        "fixes_alpha": False,
        "full_no_fit": False,
        "needs": ["non-observational boundary charge", "reference state"],
        "meaning": "alpha can be read from a Hamiltonian/Noether charge, but the charge is the same missing state datum.",
        "bibliography": ["Brown-York 1993", "Iyer-Wald 1993/1994"],
    },
    {
        "id": "souriau_coadjoint_orbit",
        "kind": "symplectic_state",
        "status": "equivalent_if_orbit_label_available",
        "fixes_alpha": False,
        "full_no_fit": False,
        "needs": ["coadjoint orbit label", "moment-map normalization"],
        "meaning": "alpha becomes a conserved orbit label. This is clean, but still a state-sector input unless quantized.",
        "bibliography": ["Souriau moment-map framework"],
    },
    {
        "id": "flux_quantization",
        "kind": "quantized_sector",
        "status": "open_but_requires_extra_structure",
        "fixes_alpha": False,
        "full_no_fit": False,
        "needs": ["U(1) or higher-form field", "charge unit", "closed cycle", "alpha-flux map"],
        "meaning": "could discretize alpha, but Janus/Z2 topology alone does not provide the flux unit.",
        "bibliography": ["standard flux compactification/moduli stabilization literature"],
    },
    {
        "id": "casimir_topological_vacuum",
        "kind": "quantum_state_energy",
        "status": "open_but_model_dependent",
        "fixes_alpha": False,
        "full_no_fit": False,
        "needs": ["field content", "renormalization prescription", "topological vacuum state"],
        "meaning": "can produce a scale-dependent vacuum energy, not a Janus-only alpha without quantum state data.",
        "bibliography": ["Casimir energy on spherical/projective topologies"],
    },
    {
        "id": "horizon_thermodynamics",
        "kind": "thermodynamic_relation",
        "status": "relation_not_selector",
        "fixes_alpha": False,
        "full_no_fit": False,
        "needs": ["entropy/microstate law", "temperature or state count"],
        "meaning": "gives first-law constraints, but does not choose the absolute scale alone.",
        "bibliography": ["Iyer-Wald", "FRW horizon thermodynamics"],
    },
    {
        "id": "moduli_stabilization_throat_potential",
        "kind": "uv_completion",
        "status": "requires_new_sector",
        "fixes_alpha": False,
        "full_no_fit": False,
        "needs": ["stabilizing potential", "flux/source sector"],
        "meaning": "physically plausible UV route, but outside current Janus/Z2/Sigma action.",
        "bibliography": ["moduli stabilization / flux compactification"],
    },
    {
        "id": "pure_topology_RP4_Sigma_Z2",
        "kind": "topology_only",
        "status": "no_go_for_dimensionful_alpha",
        "fixes_alpha": False,
        "full_no_fit": False,
        "needs": [],
        "meaning": "topology fixes ratios/parity/covering, not a dimensionful length.",
        "bibliography": ["dimension analysis"],
    },
    {
        "id": "observational_H0_or_SN_offset",
        "kind": "observational_calibration",
        "status": "forbidden_for_no_rustine_core",
        "fixes_alpha": True,
        "full_no_fit": False,
        "needs": ["H0 or distance-modulus offset"],
        "meaning": "valid phenomenology, but not a no-rustine derivation.",
        "bibliography": ["published Janus SN fit route"],
    },
    {
        "id": "planck_area_gap_or_quantum_gravity_unit",
        "kind": "quantum_gravity_postulate",
        "status": "new_axiom_unless_derived",
        "fixes_alpha": False,
        "full_no_fit": False,
        "needs": ["area spectrum", "map A_Sigma -> alpha", "sector N"],
        "meaning": "could fix alpha if a quantum geometry law is accepted, but that is not yet derived from Janus.",
        "bibliography": ["isolated horizon/LQG area literature"],
    },
]


def build_payload() -> dict[str, Any]:
    usable = [route for route in ROUTES if route["status"] == "usable_conditional_solution"]
    no_go = [route["id"] for route in ROUTES if route["status"].startswith("no_go")]
    return {
        "status": "janus-z2-alpha-solution-search-gate",
        "active_core": "Z2_tunnel_Sigma",
        "routes_tested_from_obvious_to_exotic": ROUTES,
        "best_current_solution": usable[0]["id"] if usable else None,
        "solution_class": "state_conditional_not_topology_predicted",
        "alpha_may_be_supplied_as_state_sector": bool(usable),
        "full_no_fit_prediction_ready": False,
        "pure_topology_can_fix_alpha": False,
        "no_go_routes": no_go,
        "next_required_input": "exact_solution_alpha_state_sector_inputs.json",
        "interpretation": (
            "The honest solution is to treat alpha_m as a global integration "
            "constant/state sector of the exact Janus solution. Boundary-charge "
            "and Souriau routes are cleaner ways to name the same datum unless "
            "a further quantization or state-selection theorem is derived."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Alpha Solution Search Gate",
        "",
        f"Best current solution: `{payload['best_current_solution']}`",
        f"Solution class: `{payload['solution_class']}`",
        f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
        "",
        "## Routes",
    ]
    lines.extend(
        f"- `{route['id']}`: `{route['status']}`" for route in payload["routes_tested_from_obvious_to_exotic"]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
