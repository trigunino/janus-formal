from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_global_bimetric_state_to_flrw_sector_normalization_gate import (
    build_payload as build_global_state,
)
from scripts.build_p0_eft_janus_z2_sigma_boundary_projection_charge_contract_gate import (
    build_payload as build_charge_contract,
)
from scripts.build_p0_eft_janus_z2_sigma_h0_boundary_hamiltonian_projection_gate import (
    build_payload as build_h0_projection,
)
from scripts.build_p0_eft_janus_z2_sigma_noether_hamiltonian_boundary_charge_gate import (
    build_payload as build_noether_charge,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_boundary_leg_evaluation_inventory_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_boundary_leg_evaluation_inventory_gate.json"
)


def build_payload() -> dict:
    h0 = build_h0_projection()
    noether = build_noether_charge()
    charge_contract = build_charge_contract()
    global_state = build_global_state()

    leg_inventory = {
        "plus_boundary_leg_declared": True,
        "minus_boundary_leg_declared": True,
        "plus_normal_orientation_required": True,
        "minus_normal_orientation_required": True,
        "lapse_time_gauge_required": True,
        "reference_subtraction_required": True,
        "joint_corner_terms_required": True,
    }
    readiness = {
        "symbolic_boundary_hamiltonian_ready": bool(
            noether["symbolic_boundary_hamiltonian_ready"]
        ),
        "h0_projection_symbolic_ready": bool(
            h0["closure"]["theta_HP_to_ADM_surface_generator_projected"]
        ),
        "boundary_projection_charge_ready": bool(
            charge_contract["projected_boundary_charge_ready"]
        ),
        "global_bimetric_state_ready": bool(global_state["sector_normalizations_ready"]),
    }
    numeric_ready = all(readiness.values())
    return {
        "status": "janus-z2-sigma-boundary-leg-evaluation-inventory-gate",
        "active_core": "Z2_tunnel_Sigma",
        "interpretation": (
            "The 'legs of each boundary' are the plus/minus boundary evaluations "
            "with their normals, lapse/time generator, reference subtraction, and "
            "possible joint/corner terms. They are necessary for a Hamiltonian "
            "boundary charge, but they do not by themselves create a FLRW source."
        ),
        "leg_inventory": leg_inventory,
        "readiness": readiness,
        "boundary_leg_symbolic_inventory_ready": all(leg_inventory.values()),
        "numeric_boundary_state_ready": numeric_ready,
        "maps_to_global_state_input": (
            "If both legs yield a nonzero renormalized boundary charge, the result "
            "can populate global_bimetric_stress_energy_state_inputs.json; until "
            "then rho_plus0/rho_minus0 remain unnormalized."
        ),
        "primary_blockers": [key for key, value in readiness.items() if not value],
        "forbidden_shortcuts": [
            "do_not_evaluate_only_one_boundary_leg",
            "do_not_use_reference_zero_as_positive_source",
            "do_not_identify_joint_corner_bookkeeping_with_new_density",
            "do_not_fit_boundary_charge_to_observations",
        ],
        "next_required": [
            "derive_active_plus_minus_boundary_leg_normals",
            "derive_active_lapse_time_generator_on_both_legs",
            "evaluate_Q_boundary_raw_minus_Q_reference_raw",
            "map_nonzero_boundary_state_to_global_bimetric_stress_energy_state_inputs",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Boundary Leg Evaluation Inventory Gate",
        "",
        payload["interpretation"],
        "",
        f"Symbolic leg inventory ready: `{payload['boundary_leg_symbolic_inventory_ready']}`",
        f"Numeric boundary state ready: `{payload['numeric_boundary_state_ready']}`",
        "",
        "## Readiness",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["readiness"].items())
    lines.extend(["", "## Primary Blockers"])
    lines.extend(f"- `{item}`" for item in payload["primary_blockers"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
