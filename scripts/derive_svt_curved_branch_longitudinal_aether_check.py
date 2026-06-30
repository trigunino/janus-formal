from __future__ import annotations

from functools import lru_cache
from pathlib import Path
import json
import os

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
REPORT_PATH = REPORT_DIR / "svt_curved_branch_longitudinal_aether_check.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_longitudinal_aether_check.json"


@lru_cache(maxsize=None)
def alpha_num_den() -> tuple[sp.Expr, sp.Expr]:
    num, den = sp.fraction(sp.factor(witness_kernels()["alpha_dS"]))
    return sp.factor(num), sp.factor(den)


def proposed_longitudinal_delta_n() -> sp.Expr:
    return 312 * A**2 * K**2


def corrected_alpha_with_proposed_delta() -> sp.Expr:
    num, den = alpha_num_den()
    return sp.factor((num + proposed_longitudinal_delta_n()) / den)


def required_delta_for_constant_alpha() -> sp.Expr:
    num, den = alpha_num_den()
    return sp.factor(5392 * den - num)


def corrected_alpha_with_required_delta() -> sp.Expr:
    num, den = alpha_num_den()
    return sp.factor((num + required_delta_for_constant_alpha()) / den)


def residual_after_proposed_delta() -> sp.Expr:
    num, den = alpha_num_den()
    return sp.factor(num + proposed_longitudinal_delta_n() - 5392 * den)


def residual_after_required_delta() -> sp.Expr:
    num, den = alpha_num_den()
    return sp.factor(num + required_delta_for_constant_alpha() - 5392 * den)


def corrected_zero_gap_with_proposed_delta() -> sp.Expr:
    num, den = alpha_num_den()
    x = sp.Symbol("x", positive=True)
    num_root = sp.solve((num + proposed_longitudinal_delta_n()).subs(K**2, x), x)[0]
    den_root = sp.solve(den.subs(K**2, x), x)[0]
    return sp.factor(den_root - num_root)


def sample_midpoint_alpha() -> str:
    sample = {A: 1, H: sp.sqrt(sp.Rational(1, 2)), K: sp.Rational(1605, 1000)}
    return str(sp.N(corrected_alpha_with_proposed_delta().subs(sample)))


def build_payload() -> dict:
    return {
        "artifact": "svt_curved_branch_longitudinal_aether_check",
        "status": "proposed_longitudinal_delta_does_not_synchronize_alpha_pole",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "proposed_delta_N": expr_text(proposed_longitudinal_delta_n()),
        "required_delta_for_alpha_5392": expr_text(required_delta_for_constant_alpha()),
        "residual_after_proposed_delta": expr_text(residual_after_proposed_delta()),
        "residual_after_required_delta": expr_text(residual_after_required_delta()),
        "corrected_alpha_with_proposed_delta": expr_text(corrected_alpha_with_proposed_delta()),
        "corrected_alpha_with_required_delta": expr_text(corrected_alpha_with_required_delta()),
        "corrected_zero_gap_with_proposed_delta": expr_text(corrected_zero_gap_with_proposed_delta()),
        "sample_alpha_near_old_band": sample_midpoint_alpha(),
        "verdict": {
            "proposed_delta_makes_alpha_5392": sp.simplify(residual_after_proposed_delta()) == 0,
            "proposed_delta_synchronizes_zeros": sp.simplify(corrected_zero_gap_with_proposed_delta()) == 0,
            "required_delta_makes_alpha_5392": sp.simplify(residual_after_required_delta()) == 0,
            "required_delta_alpha_constant": sp.simplify(corrected_alpha_with_required_delta() - 5392) == 0,
            "prediction_ready": False,
            "reason": (
                "The exact required DeltaN closes alpha algebraically, but this "
                "artifact treats that DeltaN as a supplied longitudinal-Aether input."
            ),
        },
        "needed_inputs": [
            "derive the longitudinal Aether contribution from the full dS Cartan-Aether action",
            "derive required_delta_for_alpha_5392 from the full dS Cartan-Aether longitudinal action",
            "then promote this conditional closure into Lean as a sourced theorem",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Longitudinal Aether Check",
        "",
        f"Status: `{payload['status']}`",
        f"Prediction ready: `{payload['verdict']['prediction_ready']}`",
        "",
        f"- proposed_delta_N: `{payload['proposed_delta_N']}`",
        f"- required_delta_for_alpha_5392: `{payload['required_delta_for_alpha_5392']}`",
        f"- residual_after_proposed_delta: `{payload['residual_after_proposed_delta']}`",
        f"- residual_after_required_delta: `{payload['residual_after_required_delta']}`",
        f"- corrected_alpha_with_required_delta: `{payload['corrected_alpha_with_required_delta']}`",
        f"- corrected_zero_gap_with_proposed_delta: `{payload['corrected_zero_gap_with_proposed_delta']}`",
        f"- sample_alpha_near_old_band: `{payload['sample_alpha_near_old_band']}`",
        "",
        "## Needed Inputs",
    ]
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
