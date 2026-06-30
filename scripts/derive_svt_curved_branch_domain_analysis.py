from __future__ import annotations

from pathlib import Path
import json
import os
from functools import lru_cache

import sympy as sp

try:
    from scripts.derive_svt_curved_branch_desitter_seed import A, H, K
    from scripts.derive_svt_curved_branch_effective_mode import witness_kernels
    from scripts.derive_svt_quadratic_coefficients import expr_text
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_curved_branch_desitter_seed import A, H, K
    from derive_svt_curved_branch_effective_mode import witness_kernels
    from derive_svt_quadratic_coefficients import expr_text


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_curved_branch_domain_analysis.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_domain_analysis.json"


@lru_cache(maxsize=None)
def alpha_witness() -> sp.Expr:
    return witness_kernels()["alpha_dS"]


@lru_cache(maxsize=None)
def alpha_num_den() -> tuple[sp.Expr, sp.Expr]:
    num, den = sp.fraction(sp.factor(alpha_witness()))
    return sp.factor(num), sp.factor(den)


@lru_cache(maxsize=None)
def alpha_zero_locations() -> dict[str, sp.Expr]:
    num, den = alpha_num_den()
    x = sp.Symbol("x", positive=True)
    num_x = num.subs(K**2, x)
    den_x = den.subs(K**2, x)
    return {
        "k2_num_zero": sp.factor(sp.solve(num_x, x)[0]),
        "k2_den_zero": sp.factor(sp.solve(den_x, x)[0]),
    }


@lru_cache(maxsize=None)
def zero_gap() -> sp.Expr:
    roots = alpha_zero_locations()
    return sp.factor(roots["k2_den_zero"] - roots["k2_num_zero"])


@lru_cache(maxsize=None)
def negative_band_sample() -> dict:
    roots = alpha_zero_locations()
    midpoint = sp.factor((roots["k2_num_zero"] + roots["k2_den_zero"]) / 2)
    sample = {
        A: 1,
        H: sp.sqrt(sp.Rational(1, 2)),
        K: sp.sqrt(midpoint.subs({A: 1, H: sp.sqrt(sp.Rational(1, 2))})),
    }
    value = sp.N(alpha_witness().subs(sample))
    return {
        "k2_midpoint": expr_text(midpoint),
        "k_midpoint_a1_HsqrtHalf": str(sp.N(sample[K])),
        "alpha_at_midpoint": str(value),
        "alpha_negative": bool(value < 0),
    }


@lru_cache(maxsize=None)
def beta_witness() -> sp.Expr:
    return witness_kernels()["beta_dS"]


@lru_cache(maxsize=None)
def build_payload() -> dict:
    num, den = alpha_num_den()
    roots = alpha_zero_locations()
    gap = zero_gap()
    band = negative_band_sample()
    return {
        "artifact": "svt_curved_branch_domain_analysis",
        "status": "global_positivity_refuted_by_narrow_negative_alpha_band",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "alpha": {
            "expr": expr_text(alpha_witness()),
            "numerator": expr_text(num),
            "denominator": expr_text(den),
            "k2_num_zero": expr_text(roots["k2_num_zero"]),
            "k2_den_zero": expr_text(roots["k2_den_zero"]),
            "gap_den_minus_num": expr_text(gap),
            "zeros_identical": sp.simplify(gap) == 0,
        },
        "beta": {
            "expr": expr_text(beta_witness()),
            "positive_for_a_positive_k_positive": True,
        },
        "negative_band": band,
        "verdict": {
            "beta_global_positive": True,
            "alpha_global_positive": False,
            "cs2_global_nonnegative": False,
            "prediction_ready": False,
            "reason": (
                "The numerator zero occurs before the denominator zero. "
                "Between them alpha_dS is negative and cs2 is negative."
            ),
        },
        "needed_inputs": [
            "a physical cutoff excluding the narrow band k_num^2 < k^2 < k_den^2, or",
            "a corrected dS action/constraint term that cancels the pole and makes the zeros identical",
            "then rerun the domain proof before Lean prediction_ready",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Domain Analysis",
        "",
        f"Status: `{payload['status']}`",
        f"Prediction ready: `{payload['verdict']['prediction_ready']}`",
        "",
        "## Alpha Zeros",
        f"- k2_num_zero: `{payload['alpha']['k2_num_zero']}`",
        f"- k2_den_zero: `{payload['alpha']['k2_den_zero']}`",
        f"- gap: `{payload['alpha']['gap_den_minus_num']}`",
        f"- zeros_identical: `{payload['alpha']['zeros_identical']}`",
        "",
        "## Negative Band",
    ]
    for key, value in payload["negative_band"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Needed Inputs"])
    lines.extend(f"- {item}" for item in payload["needed_inputs"])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
