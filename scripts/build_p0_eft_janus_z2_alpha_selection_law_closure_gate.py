from __future__ import annotations

import json
from pathlib import Path
from typing import Any


JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_alpha_selection_law_closure_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_alpha_selection_law_closure_gate.md")


ROUTES: list[dict[str, Any]] = [
    {
        "id": "boundary_charge",
        "selection_equation": "alpha_m = -2*pi*G*M_boundary/c^2",
        "new_unknowns": ["M_boundary"],
        "verdict": "relabels_state_sector",
        "reason": "No Janus/Z2 theorem fixes M_boundary.",
    },
    {
        "id": "souriau_orbit",
        "selection_equation": "alpha_m = -2*pi*G*mu_orbit/c^2",
        "new_unknowns": ["mu_orbit"],
        "verdict": "relabels_state_sector",
        "reason": "Coadjoint mass/orbit label is continuous unless an extra integrality law is supplied.",
    },
    {
        "id": "flux_quantization",
        "selection_equation": "alpha_n = gamma_flux*q_unit*n",
        "new_unknowns": ["gamma_flux", "q_unit", "n"],
        "verdict": "requires_extra_quantum_structure",
        "reason": "Z2/Sigma supplies a cycle but not a normalized gauge field or alpha-flux map.",
    },
    {
        "id": "casimir_topology",
        "selection_equation": "alpha_m^2 = -2*pi*kappa_C*l_P^2",
        "new_unknowns": ["kappa_C"],
        "verdict": "requires_extra_quantum_state",
        "reason": "Needs field content, sign, spin structure and renormalized vacuum coefficient.",
    },
    {
        "id": "horizon_thermodynamics",
        "selection_equation": "dE = T dS + work terms",
        "new_unknowns": ["S(A)", "T_or_state_count"],
        "verdict": "relation_not_selector",
        "reason": "First-law form constrains variations but does not select a unique alpha.",
    },
    {
        "id": "global_regular_tunnel",
        "selection_equation": "defect(alpha)=0",
        "new_unknowns": ["dimensionful_boundary_condition"],
        "verdict": "scale_invariant_without_extra_length",
        "reason": "Regularity removes defects but leaves homothetic rescaling free in pure GR/Z2.",
    },
    {
        "id": "planck_area_gap",
        "selection_equation": "4*pi*alpha_m^2 = N*A_gap",
        "new_unknowns": ["N", "A_gap", "map_alpha_to_area"],
        "verdict": "new_axiom_unless_derived",
        "reason": "Requires importing a quantum area spectrum and fixing the sector N.",
    },
]


def build_payload() -> dict[str, Any]:
    unresolved = [route for route in ROUTES if route["verdict"] != "closed_unique_alpha"]
    return {
        "status": "janus-z2-alpha-selection-law-closure-gate",
        "active_core": "Z2_tunnel_Sigma",
        "selection_routes": ROUTES,
        "unique_alpha_selector_derived": False,
        "alpha_state_sector_remains_required": True,
        "strongest_closed_statement": (
            "Within the current Janus/Z2/Sigma action data, alpha_m can be a "
            "legitimate global state/integration constant, but no internal law "
            "selects or quantizes its value."
        ),
        "non_rustine_positive_result": (
            "Use alpha_m as a state sector and propagate conditional predictions."
        ),
        "not_yet_available": [
            "boundary charge value",
            "Souriau orbit quantization",
            "normalized flux-to-alpha map",
            "Janus Casimir coefficient",
            "quantum area sector selector",
        ],
        "unresolved_route_ids": [route["id"] for route in unresolved],
        "full_no_fit_prediction_ready": False,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Alpha Selection Law Closure Gate",
        "",
        f"Unique alpha selector derived: `{payload['unique_alpha_selector_derived']}`",
        f"Alpha state sector required: `{payload['alpha_state_sector_remains_required']}`",
        "",
        payload["strongest_closed_statement"],
        "",
        "## Routes",
    ]
    lines.extend(
        f"- `{route['id']}`: `{route['verdict']}` via `{route['selection_equation']}`"
        for route in payload["selection_routes"]
    )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
