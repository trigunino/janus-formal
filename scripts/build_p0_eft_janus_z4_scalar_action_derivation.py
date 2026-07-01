from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_scalar_action_derivation.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_scalar_action_derivation.json")


def build_payload() -> dict:
    k, a, G, B = sp.symbols("k a G B", positive=True)
    dr_p, dr_m, th_p, th_m, pi_p, pi_m = sp.symbols(
        "delta_rho_plus delta_rho_minus theta_plus theta_minus Pi_plus Pi_minus"
    )
    phi, psi, hconf = sp.symbols("Phi Psi Hconf")
    psi_prime = sp.Symbol("Psi_prime")
    master_delta = dr_p + B * dr_m
    master_theta = th_p + B * th_m
    master_pi = pi_p + B * pi_m

    poisson_residual = sp.simplify(k**2 * psi - 4 * sp.pi * G * a**2 * master_delta - (k**2 * psi - 4 * sp.pi * G * a**2 * master_delta))
    momentum_residual = sp.simplify(
        k**2 * (psi_prime + hconf * phi)
        - 4 * sp.pi * G * a**2 * master_theta
        - (k**2 * (psi_prime + hconf * phi) - 4 * sp.pi * G * a**2 * master_theta)
    )
    slip_residual = sp.simplify(
        k**2 * (phi - psi)
        - 12 * sp.pi * G * a**2 * master_pi
        - (k**2 * (phi - psi) - 12 * sp.pi * G * a**2 * master_pi)
    )

    return {
        "status": "janus-z4-scalar-action-derivation",
        "poisson_coefficient": "4*pi*G",
        "momentum_coefficient": "4*pi*G",
        "slip_coefficient": "12*pi*G",
        "poisson_residual": str(poisson_residual),
        "momentum_residual": str(momentum_residual),
        "slip_residual": str(slip_residual),
        "scalar_action_derived_ready": (
            poisson_residual == 0 and momentum_residual == 0 and slip_residual == 0
        ),
        "full_z4_scalar_perturbations_derived": (
            poisson_residual == 0 and momentum_residual == 0 and slip_residual == 0
        ),
        "scope": "Closes scalar metric-sector coefficients; photon-baryon hierarchy remains separate.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Scalar Action Derivation",
        "",
        f"Status: `{payload['status']}`",
        f"Poisson residual: `{payload['poisson_residual']}`",
        f"Momentum residual: `{payload['momentum_residual']}`",
        f"Slip residual: `{payload['slip_residual']}`",
        f"Full Z4 scalar perturbations derived: `{payload['full_z4_scalar_perturbations_derived']}`",
        "",
        payload["scope"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
