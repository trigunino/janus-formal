from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_lapse_time_gauge_route_decision_gate import (
    build_payload as build_lapse_route,
)
from scripts.build_p0_eft_janus_z2_sigma_boundary_reference_subtraction_gate import (
    build_payload as build_reference_subtraction,
)
from scripts.build_p0_eft_janus_z2_sigma_brown_york_boundary_charge_reduction_gate import (
    build_payload as build_brown_york_charge,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_h0_surface_energy_normalization_frontier_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_h0_surface_energy_normalization_frontier_gate.json"
)


def build_payload() -> dict:
    lapse_route = build_lapse_route()
    reference = build_reference_subtraction()
    brown_york = build_brown_york_charge()
    closure = {
        "branch_lapse_convention_fixed_for_FLRW": bool(
            lapse_route["can_fix_branch_lapse_for_FLRW_background"]
        ),
        "boundary_reference_zero_point_fixed": bool(reference["zero_point_fixed"]),
        "brown_york_charge_formula_reduced": True,
        "brown_york_charge_inputs_complete": bool(
            brown_york["boundary_charge_reduction_ready"]
        ),
        "on_shell_Hamiltonian_constraint_value_available": False,
        "Z2Sigma_boundary_surface_energy_normalization_available": False,
        "absolute_time_or_length_scale_available": False,
        "H0_normalization_inputs_writable": False,
    }
    return {
        "status": "janus-z2-sigma-h0-surface-energy-normalization-frontier-gate",
        "active_core": "Z2_tunnel_Sigma",
        "frontier": "boundary_surface_energy_normalization",
        "reading_rule": (
            "The FLRW proper-time gauge fixes a lapse convention, not the physical "
            "dimensionful H0 scale. H0_Z2Sigma requires an on-shell Hamiltonian "
            "constraint value plus a Z2/Sigma boundary surface-energy normalization."
        ),
        "closure": closure,
        "ready_for_background_H0_input": all(closure.values()),
        "blocked_outputs": [
            "background_H0_normalization_inputs.json",
            "background_scalars.json",
            "dimensionful_R_curv_Z2Sigma_m",
        ],
        "allowed_now": [
            "dimensionless_FLRW_lapse_convention_N_equals_1",
            "scale_free_curvature_relations",
            "boundary_Hamiltonian_slot_accounting",
            "quasilocal_reference_zero_subtraction",
        ],
        "forbidden_shortcuts": [
            "do_not_promote_N_equals_1_to_numeric_H0",
            "do_not_read_H0_from_observational_best_fit",
            "do_not_use_counterterm_zero_as_surface_energy_normalization",
            "do_not_choose_arbitrary_boundary_energy_density",
        ],
        "next_required": [
            "derive_absolute_R_Sigma_or_active_surface_measure",
            "derive_k_ref_minus_k_phys_on_active_Z2Sigma_time_leaf",
            "derive_boundary_charge_above_reference_vacuum_on_active_Z2Sigma_branch",
            "map_boundary_charge_to_H0_Z2Sigma_normalization",
            "then_write_background_H0_normalization_inputs_json",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma H0 Surface-Energy Normalization Frontier Gate",
        "",
        payload["reading_rule"],
        "",
        f"Ready for H0 input: `{payload['ready_for_background_H0_input']}`",
        "",
        "## Closure",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["closure"].items())
    lines.extend(["", "## Blocked Outputs"])
    lines.extend(f"- `{item}`" for item in payload["blocked_outputs"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
