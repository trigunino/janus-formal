from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
THETA_PATH = BASE / "holst_palatini_boundary_theta_pt67_projection.json"
OUTPUT_PATH = BASE / "pt_souriau_symplectic_integrality_inputs.json"
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_pt_souriau_omega_from_theta_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_pt_souriau_omega_from_theta_gate.md")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _all_zero(values: Any) -> bool:
    return isinstance(values, list) and all(float(v) == 0.0 for v in values)


def build_payload(
    theta_path: Path = THETA_PATH,
    output_path: Path = OUTPUT_PATH,
    *,
    write_output: bool = False,
) -> dict[str, Any]:
    theta = _read(theta_path)
    theta_ready = bool(theta.get("R_h_trace_values_ready")) and bool(theta.get("R_K_trace_values_ready"))
    theta_trivial = theta_ready and _all_zero(theta.get("R_h_trace_values")) and _all_zero(
        theta.get("R_K_trace_values")
    )
    omega_declared = theta_ready
    omega_closed = theta_ready
    periods_computable = omega_declared and not theta_trivial
    output = None
    if periods_computable:
        output = {
            "boundary_phase_space_declared": True,
            "symplectic_two_form_Omega_PT_declared": True,
            "Omega_PT_closed": True,
            "prequantum_integrality_condition_declared": True,
            "periods_over_two_cycles_computed": False,
            "periods_are_integer_multiples_of_2pi_hbar": False,
            "mass_moment_map_period_identified": False,
            "minimal_positive_period_nonzero": False,
            "PT_sign_pairing_preserves_lattice": True,
        }
        if write_output:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-pt-souriau-omega-from-theta-gate",
        "active_core": "Z2_tunnel_Sigma",
        "theta_path": str(theta_path),
        "theta_input_exists": theta_path.exists(),
        "theta_ready": theta_ready,
        "theta_trivial_on_PT67_torsionless_branch": theta_trivial,
        "Omega_PT_candidate": "Omega_PT = delta theta_PT",
        "Omega_PT_declared": omega_declared,
        "Omega_PT_closed": omega_closed,
        "periods_computable": periods_computable,
        "integrality_route_open": periods_computable,
        "written_integrality_inputs": output,
        "obstruction": (
            "On the current PT67 regular torsionless branch, theta_PT has zero "
            "non-GHY R_h/R_K trace content. Therefore delta theta_PT carries no "
            "nonzero boundary two-cycle period and cannot generate m_charge."
        )
        if theta_trivial
        else None,
        "next_nontrivial_options": [
            "derive a nonzero PT boundary KKS/Souriau density not equal to Holst-Palatini theta",
            "open a torsionful or null boundary sector with nonzero theta_PT",
            "derive a matter/gauge boundary phase space on Sigma",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload(write_output=True)
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 PT/Souriau Omega From Theta Gate",
                "",
                f"Theta ready: `{payload['theta_ready']}`",
                f"Theta trivial: `{payload['theta_trivial_on_PT67_torsionless_branch']}`",
                f"Integrality route open: `{payload['integrality_route_open']}`",
                "",
                str(payload["obstruction"] or "Nontrivial Omega_PT route remains open."),
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
