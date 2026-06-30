from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_pressure_pi_omega_extension_blocker.md")
JSON_PATH = Path("outputs/reports/p0_pressure_pi_omega_extension_blocker.json")


def build_payload() -> dict:
    remaining_tensor_terms = [
        "perfect-fluid pressure projector term p h^{mu nu}",
        "pressure gradient D p in the Euler/force balance",
        "projector transport for h^{mu nu}=g^{mu nu}+u^mu u^nu",
        "anisotropic stress Pi^{mu nu}",
        "covariant divergence nabla_mu Pi^{mu nu}",
        "equation of state and cross-pressure closure for p and p_cross",
    ]
    forbidden_shortcuts = [
        "do not absorb p h^{mu nu} into scalar Q_det",
        "do not absorb Pi^{mu nu} or div Pi into scalar Q_cross",
        "do not treat Omega_u u=0 rank-one dust closure as perfect-fluid closure",
        "do not hide equation-of-state or cross-pressure terms in scalar calibration",
    ]
    closure_gates = {
        "rank_one_dust_omega_closed": True,
        "pressure_projector_transport_closed": False,
        "pressure_gradient_closed": False,
        "pi_transport_or_zero_proof_closed": False,
        "pi_divergence_closed": False,
        "eos_cross_pressure_closed": False,
        "scalar_absorption_allowed": False,
    }
    return {
        "description": "Bounded P0 blocker for extending Omega_u u=0 rank-one dust closure to pressure and anisotropic stress.",
        "status": "extension-blocked",
        "rank_one_dust_omega_closure_insufficient": True,
        "remaining_tensor_terms": remaining_tensor_terms,
        "forbidden_shortcuts": forbidden_shortcuts,
        "closure_gates": closure_gates,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Omega_u u=0 closes only the rank-one dust Omega residual. Perfect-fluid "
            "pressure and anisotropic stress introduce tensor projector, gradient, "
            "transport, divergence, and equation-of-state data that cannot be absorbed "
            "into scalar Q_det or Q_cross."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Pressure/Pi Omega Extension Blocker",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Rank-one dust Omega closure insufficient: {payload['rank_one_dust_omega_closure_insufficient']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Remaining Tensor Terms",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["remaining_tensor_terms"])
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.extend(["", "## Closure Gates", ""])
    lines.extend(f"- {key}: {value}" for key, value in payload["closure_gates"].items())
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
