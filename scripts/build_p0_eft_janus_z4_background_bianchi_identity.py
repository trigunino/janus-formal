from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_background_bianchi_identity.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_background_bianchi_identity.json")


def build_payload() -> dict:
    G, B = sp.symbols("G B")
    rho_p, rho_m, p_p, p_m, H = sp.symbols("rho_plus rho_minus p_plus p_minus H", nonzero=True)
    C = sp.Rational(8, 3) * sp.pi * G
    rho = rho_p + B * rho_m
    pressure = p_p + B * p_m
    rho_dot = -3 * H * (rho + pressure)
    hdot_from_friedmann = sp.simplify(C * rho_dot / (2 * H))
    raychaudhuri = sp.simplify(-4 * sp.pi * G * (rho + pressure))
    residual = sp.simplify(hdot_from_friedmann - raychaudhuri)

    return {
        "status": "janus-z4-background-bianchi-identity",
        "master_density": str(rho),
        "master_pressure": str(pressure),
        "rho_dot": str(rho_dot),
        "hdot_from_friedmann": str(hdot_from_friedmann),
        "raychaudhuri_target": str(raychaudhuri),
        "residual": str(residual),
        "background_bianchi_identity_ready": residual == 0,
        "no_extra_background_fluid_introduced": True,
        "coefficients_from_full_action": False,
        "full_z4_background_system_derived": False,
        "next_required": (
            "Derive the same Friedmann coefficient from the nonlinear Z4 action "
            "instead of taking it as the Einstein-Palatini normalization."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Background Bianchi Identity",
        "",
        f"Status: `{payload['status']}`",
        f"Residual: `{payload['residual']}`",
        f"Bianchi identity ready: `{payload['background_bianchi_identity_ready']}`",
        f"Full Z4 background system derived: `{payload['full_z4_background_system_derived']}`",
        "",
        "## Equations",
        "",
        f"- master density: `{payload['master_density']}`",
        f"- master pressure: `{payload['master_pressure']}`",
        f"- rho dot: `{payload['rho_dot']}`",
        f"- H dot from Friedmann: `{payload['hdot_from_friedmann']}`",
        f"- Raychaudhuri target: `{payload['raychaudhuri_target']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
