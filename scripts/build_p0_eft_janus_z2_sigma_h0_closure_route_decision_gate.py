from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_brown_york_k_difference_symbolic_gate import (
    build_payload as build_brown_york,
)
from scripts.build_p0_eft_janus_z2_cover_absolute_scale_descent_gate import (
    build_payload as build_cover_scale,
)
from scripts.build_p0_eft_janus_z2_sigma_hamiltonian_charge_to_friedmann_h0_map_gate import (
    build_payload as build_hamiltonian_to_h0,
)
from scripts.build_p0_eft_janus_z2_sigma_h0_numeric_input_frontier_gate import (
    build_payload as build_h0_input_frontier,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_h0_closure_route_decision_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_h0_closure_route_decision_gate.json")


def build_payload() -> dict:
    by = build_brown_york()
    cover = build_cover_scale()
    hmap = build_hamiltonian_to_h0()
    frontier = build_h0_input_frontier()
    routes = {
        "A_action_scale": {
            "requires": ["ell_scale", "R_Sigma", "E_ct(R_Sigma, ell_scale)"],
            "available_now": False,
            "blocker": "no action-derived ell_scale or counterterm energy map",
            "acceptable": True,
        },
        "B_quasilocal_reference": {
            "requires": ["R_Sigma", "R_ref", "Hamiltonian_to_H0_map"],
            "available_now": False,
            "zero_reference_fixed": True,
            "symbolic_energy": by["formulas"]["E_BY_for_eps_minus_one"],
            "direct_H0_formula_dimensionally_valid": False,
            "blocker": "reference fixes zero and k_ref, not the energy-to-H0 conversion",
            "acceptable": True,
        },
        "C_state_charge": {
            "requires": ["Q_on_shell", "Q_ref", "N_occ", "Hamiltonian_to_H0_map"],
            "available_now": False,
            "blocker": "no state/Noether charge normalization currently supplied",
            "acceptable": True,
        },
    }
    return {
        "status": "janus-z2-sigma-h0-closure-route-decision-gate",
        "active_core": "Z2_tunnel_Sigma",
        "decision": (
            "Route B remains the shortest route for fixing the boundary reference, "
            "but it does not by itself produce H0_Z2Sigma. The direct formula "
            "H0 = 12*pi^2/kappa*(R_Sigma^2-R_ref^2) is treated as an energy "
            "difference, not a Hubble rate. The Hamiltonian-to-Friedmann map is "
            "now symbolic-ready, but numeric H0 is blocked by absent dimensionful input."
        ),
        "routes": routes,
        "cover_absolute_scale_available": cover["absolute_scale_can_descend_from_cover"],
        "hamiltonian_to_friedmann_map_symbolic_ready": hmap["symbolic_map_ready"],
        "hamiltonian_to_friedmann_map_numeric_ready": hmap["numeric_H0_ready"],
        "h0_numeric_inputs_available": frontier["numeric_H0_inputs_available"],
        "can_provide_absolute_RSigma": frontier["can_provide_absolute_RSigma"],
        "can_provide_state_charge": frontier["can_provide_state_charge"],
        "can_provide_action_scale": frontier["can_provide_action_scale"],
        "selected_next_route": "B_quasilocal_reference_plus_Hamiltonian_to_Friedmann_map",
        "H0_Z2Sigma_closure_ready": False,
        "next_required": [
            "derive_or_supply_absolute_R_Sigma_or_state_charge_or_action_scale",
            "derive_effective_volume_and_curvature_radius_or_flat_limit",
            "only_then_write_background_H0_normalization_inputs_json",
        ],
        "forbidden_shortcuts": [
            "do_not_identify_energy_dimension_with_H0_dimension",
            "do_not_use_R_ref_equals_R_sigma_zero_energy_as_nonzero_H0",
            "do_not_insert_ell_scale_without_action_derivation",
            "do_not_insert_Q_on_shell_without_state_derivation",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma H0 Closure Route Decision Gate",
        "",
        payload["decision"],
        "",
        f"Selected next route: `{payload['selected_next_route']}`",
        f"H0 closure ready: `{payload['H0_Z2Sigma_closure_ready']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
