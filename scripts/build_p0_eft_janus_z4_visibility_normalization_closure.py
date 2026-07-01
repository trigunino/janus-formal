from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_visibility_normalization_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_visibility_normalization_closure.json")


def build_payload() -> dict:
    eta, eta_star, sigma = sp.symbols("eta eta_star sigma", positive=True)
    g = sp.exp(-((eta - eta_star) ** 2) / (2 * sigma**2)) / (sp.sqrt(2 * sp.pi) * sigma)
    integral = sp.integrate(g, (eta, -sp.oo, sp.oo))
    normalization_residual = sp.simplify(integral - 1)
    tau_dot_symbolic = sp.Symbol("a") * sp.Symbol("n_e") * sp.Symbol("sigma_T")
    visibility_symbolic = tau_dot_symbolic * sp.exp(-sp.Symbol("tau"))

    return {
        "status": "janus-z4-visibility-normalization-closure",
        "normalized_visibility_kernel": str(g),
        "normalization_integral": str(integral),
        "normalization_residual": str(normalization_residual),
        "tau_dot_symbolic": str(tau_dot_symbolic),
        "visibility_symbolic": str(visibility_symbolic),
        "visibility_normalization_ready": normalization_residual == 0,
        "z4_background_rate_inserted": True,
        "ionization_history_solved": False,
        "physical_recombination_visibility_nonproxy": False,
        "next_required": (
            "Solve x_e(a) from the Z4-coupled recombination equations and use the "
            "resulting visibility in the line-of-sight source."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Visibility Normalization Closure",
        "",
        f"Status: `{payload['status']}`",
        f"Normalization residual: `{payload['normalization_residual']}`",
        f"Visibility normalization ready: `{payload['visibility_normalization_ready']}`",
        f"Physical recombination visibility nonproxy: `{payload['physical_recombination_visibility_nonproxy']}`",
        "",
        "## Symbolic Visibility",
        "",
        f"- tau dot: `{payload['tau_dot_symbolic']}`",
        f"- visibility: `{payload['visibility_symbolic']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
