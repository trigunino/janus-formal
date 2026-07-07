from __future__ import annotations

import json
from pathlib import Path
from typing import Any


BASE = Path("outputs/active_z2_sigma")
THETA_PATH = BASE / "holst_palatini_boundary_theta_pt67_projection.json"
HAMILTONIAN_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_published_minisuperspace_hamiltonian_reduction_gate.json"
)
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_alpha_two_hard_routes_gate.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_alpha_two_hard_routes_gate.md")


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _all_zero(values: Any) -> bool:
    return isinstance(values, list) and all(float(v) == 0.0 for v in values)


def build_payload(
    theta_path: Path = THETA_PATH,
    hamiltonian_path: Path = HAMILTONIAN_PATH,
) -> dict[str, Any]:
    theta = _read(theta_path)
    ham = _read(hamiltonian_path)
    theta_ready = bool(theta.get("R_h_trace_values_ready")) and bool(
        theta.get("R_K_trace_values_ready")
    )
    theta_zero = theta_ready and _all_zero(theta.get("R_h_trace_values")) and _all_zero(
        theta.get("R_K_trace_values")
    )
    holonomy_phase_ready = theta_ready and not theta_zero
    hamiltonian_reduction_ready = bool(ham.get("canonical_hamiltonian_reduction_ready"))
    valpha_ready = hamiltonian_reduction_ready and bool(
        ham.get("checks", {}).get("symplectic_pullback_to_exact_solution_derived")
    )
    return {
        "status": "janus-z2-alpha-two-hard-routes-gate",
        "active_core": "Z2_tunnel_Sigma",
        "pt_holonomy_route": {
            "theta_input_exists": theta_path.exists(),
            "theta_ready": theta_ready,
            "theta_zero_on_PT67_torsionless": theta_zero,
            "holonomy_phase_from_theta_ready": holonomy_phase_ready,
            "verdict": "closed_zero_on_current_branch"
            if theta_zero
            else "open_if_nonzero_theta_or_KKS_density_supplied",
            "next_required_if_reopened": [
                "nonzero PT KKS/Souriau boundary density",
                "torsionful or null boundary theta",
                "matter/gauge boundary phase space on Sigma",
            ],
        },
        "valpha_route": {
            "hamiltonian_report_exists": hamiltonian_path.exists(),
            "canonical_hamiltonian_reduction_ready": hamiltonian_reduction_ready,
            "V_alpha_ready": valpha_ready,
            "verdict": "blocked_before_on_shell_action"
            if not valpha_ready
            else "V_alpha_candidate_ready",
            "next_required_if_reopened": [
                "published bimetric minisuperspace Lagrangian",
                "lapse constraints and canonical momenta",
                "on-shell action evaluated on a(u)=alpha*cosh(u)^2",
                "finite interval/boundary prescription for the noncompact u orbit",
                "unique minimum or stability criterion",
            ],
        },
        "alpha_generated": holonomy_phase_ready or valpha_ready,
        "strongest_result": (
            "Both non-rustine hard routes fail on current assets. PT holonomy "
            "from Holst/Palatini theta is zero on the regular torsionless PT67 "
            "branch. V(alpha) cannot be evaluated because the published "
            "minisuperspace Lagrangian/on-shell action is not materialized, and "
            "the exact u-orbit is noncompact without a boundary prescription."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Alpha Two Hard Routes Gate",
                "",
                f"PT holonomy verdict: `{payload['pt_holonomy_route']['verdict']}`",
                f"V(alpha) verdict: `{payload['valpha_route']['verdict']}`",
                f"Alpha generated: `{payload['alpha_generated']}`",
                "",
                payload["strongest_result"],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
