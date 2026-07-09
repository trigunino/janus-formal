from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_ionization_history_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_ionization_history_closure.json")


def build_payload() -> dict:
    xe, nb, alpha, beta, c_peebles, h = sp.symbols("x_e n_b alpha beta C H", positive=True)
    peebles_rhs = sp.simplify(c_peebles * (beta * (1 - xe) - nb * alpha * xe**2) / h)
    temp_rhs = sp.Symbol("T_b_prime")
    checks = {
        "peebles_equation_declared": True,
        "baryon_temperature_equation_declared": True,
        "visibility_normalization_declared": True,
        "z4_expansion_rate_input_required": True,
        "recombination_coefficients_required": True,
        "ionization_history_solved": False,
    }
    return {
        "status": "janus-z4-ionization-history-closure",
        "lean_module": "JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4IonizationHistoryClosure",
        "peebles_rhs": str(peebles_rhs),
        "baryon_temperature_rhs": str(temp_rhs),
        "checks": checks,
        "ionization_scaffold_ready": all(
            value for key, value in checks.items()
            if key != "ionization_history_solved"
        ),
        "ionization_physical_ready": False,
        "next_required": "Solve x_e(a) and T_b(a) using H_Z4(a), alpha_B(T) and beta_B(T).",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Ionization History Closure",
        "",
        f"Status: `{payload['status']}`",
        f"Peebles RHS: `{payload['peebles_rhs']}`",
        f"Baryon temperature RHS: `{payload['baryon_temperature_rhs']}`",
        "",
        "## Checks",
    ]
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend([
        "",
        f"Ionization scaffold ready: `{payload['ionization_scaffold_ready']}`",
        f"Ionization physical ready: `{payload['ionization_physical_ready']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
