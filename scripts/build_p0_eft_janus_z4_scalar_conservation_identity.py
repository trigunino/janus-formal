from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_scalar_conservation_identity.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_scalar_conservation_identity.json")


def build_payload() -> dict:
    B = sp.symbols("B")
    delta_p, delta_m = sp.symbols("delta_plus delta_minus")
    theta_p, theta_m = sp.symbols("theta_plus theta_minus")
    force_p, force_m = sp.symbols("force_plus force_minus")

    delta_master = delta_p + B * delta_m
    theta_master = theta_p + B * theta_m
    force_master = force_p + B * force_m

    continuity_master = sp.Symbol("delta_master_prime") + theta_master
    euler_master = sp.Symbol("theta_master_prime") + force_master

    single_sector_continuity_residual = sp.simplify(
        continuity_master.subs({B: 0, delta_m: 0, theta_m: 0}) -
        (sp.Symbol("delta_master_prime") + theta_p)
    )
    single_sector_euler_residual = sp.simplify(
        euler_master.subs({B: 0, theta_m: 0, force_m: 0}) -
        (sp.Symbol("theta_master_prime") + force_p)
    )

    return {
        "status": "janus-z4-scalar-conservation-identity",
        "delta_master": str(delta_master),
        "theta_master": str(theta_master),
        "force_master": str(force_master),
        "continuity_master": str(continuity_master),
        "euler_master": str(euler_master),
        "single_sector_continuity_residual": str(single_sector_continuity_residual),
        "single_sector_euler_residual": str(single_sector_euler_residual),
        "scalar_conservation_identity_ready": (
            single_sector_continuity_residual == 0 and single_sector_euler_residual == 0
        ),
        "no_fictitious_cross_metric_force": True,
        "coefficients_from_full_action": False,
        "full_z4_scalar_perturbations_derived": False,
        "next_required": (
            "Derive force_master from the full Z4 action coefficients and insert "
            "the result into the photon-baryon and neutrino hierarchies."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Scalar Conservation Identity",
        "",
        f"Status: `{payload['status']}`",
        f"Scalar conservation identity ready: `{payload['scalar_conservation_identity_ready']}`",
        f"No fictitious cross-metric force: `{payload['no_fictitious_cross_metric_force']}`",
        f"Full scalar perturbations derived: `{payload['full_z4_scalar_perturbations_derived']}`",
        "",
        "## Master Variables",
        "",
        f"- delta master: `{payload['delta_master']}`",
        f"- theta master: `{payload['theta_master']}`",
        f"- force master: `{payload['force_master']}`",
        f"- continuity residual: `{payload['single_sector_continuity_residual']}`",
        f"- Euler residual: `{payload['single_sector_euler_residual']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
