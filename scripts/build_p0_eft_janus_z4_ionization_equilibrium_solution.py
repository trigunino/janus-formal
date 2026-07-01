from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_ionization_equilibrium_solution.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_ionization_equilibrium_solution.json")


def build_payload() -> dict:
    alpha, beta, nb = sp.symbols("alpha beta n_b", positive=True)
    xe = sp.symbols("x_e", real=True)
    stationary = beta * (1 - xe) - alpha * nb * xe**2
    roots = sp.solve(sp.Eq(stationary, 0), xe)
    positive_root = sp.simplify((-beta + sp.sqrt(beta**2 + 4 * alpha * beta * nb)) / (2 * alpha * nb))
    root_residual = sp.simplify(stationary.subs(xe, positive_root))
    low_bound_residual = sp.simplify(positive_root)
    high_bound_residual = sp.simplify(1 - positive_root)

    return {
        "status": "janus-z4-ionization-equilibrium-solution",
        "stationary_equation": str(stationary),
        "roots": [str(root) for root in roots],
        "positive_root": str(positive_root),
        "root_residual": str(root_residual),
        "low_bound_expression": str(low_bound_residual),
        "high_bound_expression": str(high_bound_residual),
        "peebles_stationary_equation_solved": root_residual == 0,
        "positive_root_selected": True,
        "root_bounded_between_zero_and_one_condition": "alpha>0, beta>0, n_b>0",
        "z4_expansion_rate_held_external": True,
        "visibility_can_use_equilibrium_root": True,
        "full_time_dependent_ionization_solved": False,
        "physical_recombination_visibility_nonproxy": False,
        "next_required": (
            "Promote the stationary root to a time-dependent x_e(a) integration "
            "with H_Z4(a), alpha_B(T_b) and beta_B(T_b)."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Ionization Equilibrium Solution",
        "",
        f"Status: `{payload['status']}`",
        f"Positive root: `{payload['positive_root']}`",
        f"Root residual: `{payload['root_residual']}`",
        f"Full time-dependent ionization solved: `{payload['full_time_dependent_ionization_solved']}`",
        "",
        "## Conditions",
        "",
        f"- bounded root condition: `{payload['root_bounded_between_zero_and_one_condition']}`",
        f"- Z4 expansion held external: `{payload['z4_expansion_rate_held_external']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
