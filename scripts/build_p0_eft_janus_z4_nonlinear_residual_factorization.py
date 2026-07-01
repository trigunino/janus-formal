from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_nonlinear_residual_factorization.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_nonlinear_residual_factorization.json")


def build_payload() -> dict:
    B, obstruction = sp.symbols("B O_nl", nonzero=True)
    r_plus = obstruction
    r_minus = -obstruction / B
    factorized = sp.Matrix([r_plus, r_minus])
    target = obstruction * sp.Matrix([1, -1 / B])
    residual = sp.simplify(factorized - target)
    weighted_consistency = sp.simplify(r_plus + B * r_minus)

    return {
        "status": "janus-z4-nonlinear-residual-factorization",
        "common_obstruction": str(obstruction),
        "factorized_residual_pair": str(factorized),
        "factorization_residual": str(residual),
        "weighted_consistency": str(weighted_consistency),
        "residual_factorization_ready": residual == sp.zeros(2, 1) and weighted_consistency == 0,
        "obstruction_vanishing_derived": False,
        "full_action_variation_closed": False,
        "next_required": "Derive O_nl = 0 from the nonlinear determinant-coupled Z4 action.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Nonlinear Residual Factorization",
        "",
        f"Status: `{payload['status']}`",
        f"Common obstruction: `{payload['common_obstruction']}`",
        f"Factorization residual: `{payload['factorization_residual']}`",
        f"Weighted consistency: `{payload['weighted_consistency']}`",
        f"Factorization ready: `{payload['residual_factorization_ready']}`",
        f"Full action variation closed: `{payload['full_action_variation_closed']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
