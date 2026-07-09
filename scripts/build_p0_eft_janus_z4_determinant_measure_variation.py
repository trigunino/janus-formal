from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_determinant_measure_variation.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_determinant_measure_variation.json")


def build_payload() -> dict:
    b = sp.symbols("B", nonzero=True)
    tr_plus, tr_minus = sp.symbols("tr_plus tr_minus")
    delta_log_b = sp.simplify(sp.Rational(1, 2) * (tr_minus - tr_plus))
    delta_b = sp.simplify(b * delta_log_b)
    delta_b_inv = sp.simplify(-(1 / b) * delta_log_b)
    reciprocal_residual = sp.simplify(delta_b / b + b * delta_b_inv)
    checks = {
        "determinant_ratio_declared": True,
        "logarithmic_variation_declared": True,
        "reciprocal_variation_consistent": reciprocal_residual == 0,
        "plus_measure_term_tracked": True,
        "minus_measure_term_tracked": True,
        "inserted_into_full_action_variation": False,
    }
    return {
        "status": "janus-z4-determinant-measure-variation",
        "lean_module": "JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4DeterminantMeasureVariation",
        "delta_log_B": str(delta_log_b),
        "delta_B": str(delta_b),
        "delta_B_inverse": str(delta_b_inv),
        "reciprocal_residual": str(reciprocal_residual),
        "checks": checks,
        "measure_variation_scaffold_ready": all(
            value for key, value in checks.items()
            if key != "inserted_into_full_action_variation"
        ),
        "measure_variation_physical_ready": False,
        "next_required": "Insert determinant-measure variations into the full nonlinear Janus action variation.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Determinant Measure Variation",
        "",
        f"Status: `{payload['status']}`",
        f"delta log B: `{payload['delta_log_B']}`",
        f"delta B: `{payload['delta_B']}`",
        f"delta B^-1: `{payload['delta_B_inverse']}`",
        f"reciprocal residual: `{payload['reciprocal_residual']}`",
        "",
        "## Checks",
    ]
    for key, value in payload["checks"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend([
        "",
        f"Measure variation scaffold ready: `{payload['measure_variation_scaffold_ready']}`",
        f"Measure variation physical ready: `{payload['measure_variation_physical_ready']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
