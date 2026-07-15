from __future__ import annotations

import json
import os
from pathlib import Path

import sympy as sp


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
B1H, B2H = sp.symbols("betaHat1 betaHat2")
TRACE2, CONTRACT2 = sp.symbols("traceSquared contractionSquared")
LAMBDA_R, LAMBDA_T = sp.symbols("lambda_r lambda_t")


def cubic_eom() -> sp.Expr:
    return sp.expand(
        B1H * (TRACE2 - CONTRACT2)
        + sp.Rational(3, 2) * B2H * (CONTRACT2 - TRACE2)
    )


def cubic_coefficient() -> sp.Expr:
    return sp.factor(B1H - sp.Rational(3, 2) * B2H)


def spherical_u2() -> sp.Expr:
    trace = LAMBDA_R + 2 * LAMBDA_T
    contraction = LAMBDA_R**2 + 2 * LAMBDA_T**2
    return sp.factor(trace**2 - contraction)


def build_payload() -> dict:
    factored = sp.factor(cubic_coefficient() * (TRACE2 - CONTRACT2))
    return {
        "artifact": "bimetric_lambda3_cubic_eom",
        "status": "dual_frame_cubic_galileon_coefficient_derived",
        "source_convention": "Noller-Scargill arXiv:1503.02700 equations 610-611",
        "raw_cubic_eom": str(cubic_eom()),
        "factored_cubic_eom": str(factored),
        "coefficient": str(cubic_coefficient()),
        "factorization_exact": sp.simplify(cubic_eom() - factored) == 0,
        "spherical_U2": str(spherical_u2()),
        "spherical_reduction": "U2=4*pi''*(pi'/r)+2*(pi'/r)^2, yielding an algebraic quadratic equation after one radial integration",
        "degenerate_surface": "betaHat1-(3/2)betaHat2=0 removes the cubic Vainshtein term",
        "closure": {
            "cubic_galileon_shape": True,
            "dual_frame_coefficient": True,
            "spherical_quadratic_reduction": True,
            "candidate_beta_normalization_map": False,
            "full_bigravity_two_frame_coefficient": False,
        },
    }


def write_report() -> dict:
    payload = build_payload()
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    (REPORT_DIR / "bimetric_lambda3_cubic_eom.json").write_text(
        json.dumps(payload, indent=2), encoding="utf-8"
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_report(), indent=2))
