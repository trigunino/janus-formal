from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_h0_boundary_hamiltonian_projection_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_h0_boundary_hamiltonian_projection_gate.json"
)


def build_payload() -> dict:
    closure = {
        "theta_HP_to_ADM_surface_generator_projected": True,
        "hamiltonian_constraint_slot_declared": True,
        "lapse_time_gauge_normalization_available": False,
        "on_shell_constraint_value_available": False,
        "surface_energy_normalization_available": False,
        "H0_Z2Sigma_numeric_ready": False,
    }
    return {
        "status": "janus-z2-sigma-h0-boundary-hamiltonian-projection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "first_order_boundary_hamiltonian_projection",
        "projection_formula": (
            "H_boundary[N] = integral_Sigma (N * H_constraint + shift^a * H_a) "
            "+ B_Sigma[N,shift]"
        ),
        "h0_reading_rule": (
            "H0_Z2Sigma is readable only after fixing the active lapse/time-gauge "
            "normalization and evaluating the on-shell Hamiltonian constraint on "
            "the active FLRW/Z2-Sigma branch."
        ),
        "closure": closure,
        "ready_for_background_H0_input": all(closure.values()),
        "forbidden_shortcuts": [
            "do_not_read_H0_from_Planck_or_LambdaCDM",
            "do_not_choose_lapse_normalization_by_fit",
            "do_not_identify_boundary_charge_with_H0_without_constraint_evaluation",
        ],
        "next_required": [
            "derive_active_lapse_time_gauge_normalization_on_Sigma",
            "evaluate_on_shell_Hamiltonian_constraint_for_active_FLRW_branch",
            "normalize_boundary_surface_energy_against_Z2Sigma_time_generator",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma H0 Boundary Hamiltonian Projection Gate",
        "",
        payload["h0_reading_rule"],
        "",
        f"Ready for H0 input: `{payload['ready_for_background_H0_input']}`",
        "",
        "## Closure",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["closure"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
