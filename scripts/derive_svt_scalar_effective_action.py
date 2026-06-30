from __future__ import annotations

from functools import lru_cache
from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import MHR2, MPL2, VEV, expr_text
    from scripts.derive_svt_scalar_exact_hr_source_reduction import (
        B_M,
        B_P,
        DPSI_M,
        DPSI_P,
        K,
        PHI_M,
        PHI_P,
        PSI_M,
        PSI_P,
        ZETA,
        exact_hr_surface_density,
        shift_solutions,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import MHR2, MPL2, VEV, expr_text
    from derive_svt_scalar_exact_hr_source_reduction import (
        B_M,
        B_P,
        DPSI_M,
        DPSI_P,
        K,
        PHI_M,
        PHI_P,
        PSI_M,
        PSI_P,
        ZETA,
        exact_hr_surface_density,
        shift_solutions,
    )


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_scalar_effective_action.md"
JSON_PATH = REPORT_DIR / "svt_scalar_effective_action.json"


def eh_plus_density() -> sp.Expr:
    return MPL2 * (
        -3 * DPSI_P**2
        + 2 * K**2 * PHI_P * PSI_P
        - K**2 * PSI_P**2
        + 2 * K**2 * DPSI_P * B_P
    )


def eh_minus_density() -> sp.Expr:
    return MPL2 * VEV * (
        -sp.Rational(3, 1) * DPSI_M**2 / VEV**2
        + 2 * K**2 * PHI_M * PSI_M / VEV**2
        - K**2 * PSI_M**2
        + 2 * K**2 * DPSI_M * B_M / VEV**2
    )


def scalar_closure_substitutions() -> dict[sp.Symbol, sp.Expr]:
    shifts = shift_solutions()
    return {
        PHI_P: sp.Integer(0),
        PHI_M: 2 * K**2 * PSI_P / (3 * MHR2 * (VEV + 1)),
        PSI_M: -PSI_P / VEV,
        DPSI_M: -DPSI_P / VEV,
        B_P: shifts["B_p"].subs({DPSI_M: -DPSI_P / VEV}),
        B_M: shifts["B_m"].subs({DPSI_M: -DPSI_P / VEV}),
        ZETA: sp.Integer(0),
    }


@lru_cache(maxsize=None)
def full_scalar_density_before_reduction() -> sp.Expr:
    return sp.factor(eh_plus_density() + eh_minus_density() + exact_hr_surface_density())


@lru_cache(maxsize=None)
def effective_scalar_density() -> sp.Expr:
    reduced = full_scalar_density_before_reduction().subs(scalar_closure_substitutions())
    return sp.factor(sp.cancel(reduced))


def effective_kernels() -> dict[str, sp.Expr]:
    density = effective_scalar_density()
    alpha = sp.factor(sp.diff(density, DPSI_P, 2) / 2)
    psi_kernel = sp.factor(sp.diff(density, PSI_P, 2) / 2)
    beta_k = sp.factor(-psi_kernel / K**2)
    return {
        "alpha_scalar_exact_k": alpha,
        "psi2_kernel": psi_kernel,
        "beta_scalar_exact_k": beta_k,
    }


def low_k_series(expr: sp.Expr, order: int = 4) -> sp.Expr:
    return sp.factor(sp.series(expr, K, 0, order).removeO())


def build_payload() -> dict:
    kernels = effective_kernels()
    return {
        "artifact": "svt_scalar_effective_action",
        "status": "scalar_eh_hr_reinjection_closed_under_supplied_gauge",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "gauge_and_constraints": {
            "psi_minus": "-psi_plus/v",
            "dpsi_minus": "-dpsi_plus/v",
            "phi_plus": "0",
            "phi_minus": "2*k^2*psi_plus/(3*mHR2*(v+1))",
            "zeta": "0",
            "shift_solutions": "from exact HR source reduction",
        },
        "effective_density": expr_text(effective_scalar_density()),
        "exact_kernels": {
            key: expr_text(value) for key, value in kernels.items()
        },
        "low_k_series": {
            "alpha_scalar": expr_text(low_k_series(kernels["alpha_scalar_exact_k"], 4)),
            "beta_scalar": expr_text(low_k_series(kernels["beta_scalar_exact_k"], 4)),
        },
        "stability_conditions": {
            "no_ghost": "alpha_scalar_exact_k > 0",
            "no_gradient": "beta_scalar_exact_k > 0",
            "poles": "denominators must avoid k^2 = 4*mHR2*v",
        },
        "closed_primitives": [
            "EH plus scalar quadratic action reinjected",
            "EH minus scalar quadratic action reinjected",
            "exact HR surface density reinjected",
            "lapse compatibility interpreted as psi_p + v*psi_m = 0",
            "visible synchronous gauge phi_p = 0 applied",
        ],
        "still_open_primitives": [
            "independent derivation of the supplied EH scalar quadratic action from Cartan variables",
            "physical domain check for the pole k^2 = 4*mHR2*v",
            "coupling of canonical radion chi and aether scalar deltaA0 to this reduced scalar gravity mode",
        ],
        "prediction_ready": False,
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Scalar Effective Action",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Exact Kernels",
    ]
    for key, value in payload["exact_kernels"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Low-k Series"])
    for key, value in payload["low_k_series"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Still Open"])
    lines.extend(f"- {item}" for item in payload["still_open_primitives"])
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
