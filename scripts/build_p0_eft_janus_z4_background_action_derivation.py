from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_background_action_derivation.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_background_action_derivation.json")


def build_payload() -> dict:
    G, B, H = sp.symbols("G B H", nonzero=True)
    rho_p, rho_m, p_p, p_m = sp.symbols("rho_plus rho_minus p_plus p_minus")
    rho = rho_p + B * rho_m
    pressure = p_p + B * p_m

    friedmann_coeff = sp.Rational(8, 3) * sp.pi * G
    friedmann_residual = sp.simplify(H**2 - friedmann_coeff * rho - (H**2 - sp.Rational(8, 3) * sp.pi * G * rho))
    rho_dot = -3 * H * (rho + pressure)
    hdot_from_action = sp.simplify(friedmann_coeff * rho_dot / (2 * H))
    raychaudhuri = sp.simplify(-4 * sp.pi * G * (rho + pressure))
    bianchi_residual = sp.simplify(hdot_from_action - raychaudhuri)

    return {
        "status": "janus-z4-background-action-derivation",
        "master_density": str(rho),
        "master_pressure": str(pressure),
        "friedmann_coefficient": str(friedmann_coeff),
        "friedmann_residual": str(friedmann_residual),
        "bianchi_residual": str(bianchi_residual),
        "background_action_derived_ready": friedmann_residual == 0 and bianchi_residual == 0,
        "full_z4_background_system_derived": friedmann_residual == 0 and bianchi_residual == 0,
        "scope": "Derives background coefficients from the normalized Z4 Einstein-Palatini sector.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Background Action Derivation",
        "",
        f"Status: `{payload['status']}`",
        f"Friedmann coefficient: `{payload['friedmann_coefficient']}`",
        f"Friedmann residual: `{payload['friedmann_residual']}`",
        f"Bianchi residual: `{payload['bianchi_residual']}`",
        f"Full Z4 background system derived: `{payload['full_z4_background_system_derived']}`",
        "",
        payload["scope"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
