from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_recombination_coefficient_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_recombination_coefficient_closure.json")


def build_payload() -> dict:
    alpha, nb, x_saha = sp.symbols("alpha n_b x_saha", positive=True)
    beta = sp.simplify(alpha * nb * x_saha**2 / (1 - x_saha))
    peebles_residual = sp.simplify(beta * (1 - x_saha) - alpha * nb * x_saha**2)
    positivity_conditions = ["alpha>0", "n_b>0", "0<x_saha<1"]

    return {
        "status": "janus-z4-recombination-coefficient-closure",
        "detailed_balance_beta": str(beta),
        "peebles_equilibrium_residual": str(peebles_residual),
        "positivity_conditions": positivity_conditions,
        "saha_equilibrium_declared": True,
        "detailed_balance_relation_declared": True,
        "peebles_equilibrium_residual_closed": peebles_residual == 0,
        "coefficients_positive": True,
        "z4_temperature_input_required": True,
        "coefficients_calibrated_from_microphysics": False,
        "physical_recombination_visibility_nonproxy": False,
        "next_required": (
            "Derive alpha_B(T_Z4) and the Saha factor from Z4 microphysics, "
            "then insert them into the time-dependent ionization ODE."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Recombination Coefficient Closure",
        "",
        f"Status: `{payload['status']}`",
        f"Detailed-balance beta: `{payload['detailed_balance_beta']}`",
        f"Peebles equilibrium residual: `{payload['peebles_equilibrium_residual']}`",
        f"Coefficients calibrated from microphysics: `{payload['coefficients_calibrated_from_microphysics']}`",
        "",
        "## Conditions",
        "",
    ]
    lines.extend(f"- `{condition}`" for condition in payload["positivity_conditions"])
    lines.extend(["", f"Next required: {payload['next_required']}", ""])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
