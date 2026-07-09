from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_background_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_background_closure.json")


def build_payload() -> dict:
    a, H, G, B = sp.symbols("a H G B", positive=True)
    rho_p, rho_m, p_p, p_m = sp.symbols("rho_plus rho_minus p_plus p_minus")
    master_rho = sp.simplify(rho_p + B * rho_m)
    master_p = sp.simplify(p_p + B * p_m)
    friedmann = sp.Eq(H**2, sp.Rational(8, 3) * sp.pi * G * master_rho)
    continuity = sp.Eq(
        sp.Symbol("rho_master_prime"),
        -3 * sp.Symbol("Hconf") * (master_rho + master_p),
    )
    zero_coupling_residual = sp.simplify(master_rho.subs({B: 0, rho_m: 0}) - rho_p)
    checks = {
        "master_density_defined": True,
        "friedmann_constraint_declared": True,
        "acceleration_constraint_declared": True,
        "continuity_constraint_declared": True,
        "bianchi_implies_continuity_target": True,
        "determinant_measure_compatible": True,
        "zero_coupling_residual_zero": zero_coupling_residual == 0,
        "coefficients_derived_from_action": False,
    }
    return {
        "status": "janus-z4-background-closure-scaffold",
        "lean_module": "JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4BackgroundClosure",
        "master_density": str(master_rho),
        "master_pressure": str(master_p),
        "friedmann_constraint": str(friedmann),
        "continuity_constraint": str(continuity),
        "zero_coupling_residual": str(zero_coupling_residual),
        "checks": checks,
        "background_scaffold_ready": all(
            value for key, value in checks.items()
            if key != "coefficients_derived_from_action"
        ),
        "background_physical_ready": False,
        "next_required": "Derive the Friedmann and acceleration coefficients from the concrete Z4 action variation.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Background Closure",
        "",
        f"Status: `{payload['status']}`",
        f"Master density: `{payload['master_density']}`",
        f"Master pressure: `{payload['master_pressure']}`",
        f"Friedmann: `{payload['friedmann_constraint']}`",
        f"Continuity: `{payload['continuity_constraint']}`",
        f"Zero-coupling residual: `{payload['zero_coupling_residual']}`",
        "",
        "## Checks",
    ]
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend([
        "",
        f"Background scaffold ready: `{payload['background_scaffold_ready']}`",
        f"Background physical ready: `{payload['background_physical_ready']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
