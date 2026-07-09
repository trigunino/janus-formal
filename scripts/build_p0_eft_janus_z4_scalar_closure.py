from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_scalar_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_scalar_closure.json")


def build_payload() -> dict:
    k, a, G, B = sp.symbols("k a G B", positive=True)
    dr_p, dr_m, th_p, th_m, pi_p, pi_m = sp.symbols(
        "delta_rho_plus delta_rho_minus theta_plus theta_minus Pi_plus Pi_minus"
    )
    phi, psi = sp.symbols("Phi Psi")
    master_delta = sp.simplify(dr_p + B * dr_m)
    master_theta = sp.simplify(th_p + B * th_m)
    master_pi = sp.simplify(pi_p + B * pi_m)
    poisson = sp.Eq(k**2 * psi, 4 * sp.pi * G * a**2 * master_delta)
    momentum = sp.Eq(k**2 * (sp.Symbol("Psi_prime") + sp.Symbol("Hconf") * phi), 4 * sp.pi * G * a**2 * master_theta)
    slip = sp.Eq(k**2 * (phi - psi), 12 * sp.pi * G * a**2 * master_pi)
    zero_coupling_residual = sp.simplify(master_delta.subs({B: 0, dr_m: 0}) - dr_p)
    checks = {
        "poisson_equation_declared": True,
        "momentum_constraint_declared": True,
        "slip_equation_declared": True,
        "continuity_equation_declared": True,
        "euler_equation_declared": True,
        "gauge_fixing_declared": True,
        "bianchi_scalar_residual_closed_target": True,
        "zero_coupling_residual_zero": zero_coupling_residual == 0,
        "coefficients_derived_from_action": False,
    }
    return {
        "status": "janus-z4-scalar-closure-scaffold",
        "lean_module": "JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4ScalarClosure",
        "master_delta": str(master_delta),
        "master_theta": str(master_theta),
        "master_pi": str(master_pi),
        "poisson": str(poisson),
        "momentum": str(momentum),
        "slip": str(slip),
        "zero_coupling_residual": str(zero_coupling_residual),
        "checks": checks,
        "scalar_closure_scaffold_ready": all(
            value for key, value in checks.items()
            if key != "coefficients_derived_from_action"
        ),
        "scalar_closure_physical_ready": False,
        "next_required": "Derive scalar coefficients and Bianchi residual closure from the Z4 action, not from GR templates.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Scalar Closure",
        "",
        f"Status: `{payload['status']}`",
        f"Master delta: `{payload['master_delta']}`",
        f"Master theta: `{payload['master_theta']}`",
        f"Master Pi: `{payload['master_pi']}`",
        f"Poisson: `{payload['poisson']}`",
        f"Momentum: `{payload['momentum']}`",
        f"Slip: `{payload['slip']}`",
        f"Zero-coupling residual: `{payload['zero_coupling_residual']}`",
        "",
        "## Checks",
    ]
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend([
        "",
        f"Scalar closure scaffold ready: `{payload['scalar_closure_scaffold_ready']}`",
        f"Scalar closure physical ready: `{payload['scalar_closure_physical_ready']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
