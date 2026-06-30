from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import MHR2, TENSION, VEV, expr_text
    from scripts.derive_svt_cartan_ghy_surface_density import trace_k_minus, trace_k_plus
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import MHR2, TENSION, VEV, expr_text
    from derive_svt_cartan_ghy_surface_density import trace_k_minus, trace_k_plus


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_cartan_spin_connection_and_background.md"
JSON_PATH = REPORT_DIR / "svt_cartan_spin_connection_and_background.json"

K = sp.Symbol("k", nonzero=True)
ZETA, DPSI_P, DPSI_M, DCHI = sp.symbols("zeta dpsi_p dpsi_m dchi")


def fourier_laplacian_zeta() -> sp.Expr:
    return -K**2 * ZETA


def omega_plus_trace() -> sp.Expr:
    return sp.factor(3 * DPSI_P + fourier_laplacian_zeta())


def omega_minus_trace() -> sp.Expr:
    return sp.factor(
        3 * DPSI_M / VEV
        + fourier_laplacian_zeta() / VEV
        - 3 * DCHI / (2 * VEV ** sp.Rational(3, 2))
    )


def k_plus_trace_from_spin_connection() -> sp.Expr:
    return sp.factor(3 * DPSI_P - fourier_laplacian_zeta())


def k_minus_trace_from_spin_connection() -> sp.Expr:
    return sp.factor(
        3 * DPSI_M / VEV
        - fourier_laplacian_zeta() / VEV
        + 3 * DCHI / (2 * VEV ** sp.Rational(3, 2))
    )


def background_delta_k() -> sp.Expr:
    return sp.factor(3 * (VEV - 1))


def background_hr_potential() -> sp.Expr:
    return sp.factor(3 * MHR2 * (VEV + 1))


def background_balance_residual() -> sp.Expr:
    return sp.factor(background_delta_k() - (TENSION - background_hr_potential()))


def required_tension_for_minkowski() -> sp.Expr:
    return sp.factor(background_delta_k() + background_hr_potential())


def build_payload() -> dict:
    witness_old = {VEV: 1, MHR2: 1, TENSION: 30}
    witness_balanced = {VEV: 1, MHR2: 1, TENSION: 6}
    return {
        "artifact": "svt_cartan_spin_connection_and_background",
        "status": "spin_connection_traces_closed_background_balance_reveals_tension_mismatch",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "spin_connection": {
            "omega_plus_trace": expr_text(omega_plus_trace()),
            "omega_minus_trace": expr_text(omega_minus_trace()),
            "fourier_convention": "partial^2 zeta -> -k^2*zeta",
        },
        "extrinsic_curvature": {
            "K_plus_trace_from_spin": expr_text(k_plus_trace_from_spin_connection()),
            "K_minus_trace_from_spin": expr_text(k_minus_trace_from_spin_connection()),
            "matches_cartan_ghy_K_plus": sp.simplify(
                k_plus_trace_from_spin_connection() - trace_k_plus()
            )
            == 0,
            "matches_cartan_ghy_K_minus": sp.simplify(
                k_minus_trace_from_spin_connection() - trace_k_minus()
            )
            == 0,
        },
        "background_balance": {
            "deltaK0": expr_text(background_delta_k()),
            "V_HR0": expr_text(background_hr_potential()),
            "residual": expr_text(background_balance_residual()),
            "required_T_memb": expr_text(required_tension_for_minkowski()),
            "old_witness_T30_residual": expr_text(background_balance_residual().subs(witness_old)),
            "balanced_witness_T6_residual": expr_text(
                background_balance_residual().subs(witness_balanced)
            ),
            "old_witness_T30_is_balanced": sp.simplify(
                background_balance_residual().subs(witness_old)
            )
            == 0,
            "balanced_witness_T6_is_balanced": sp.simplify(
                background_balance_residual().subs(witness_balanced)
            )
            == 0,
        },
        "closed_primitives": [
            "K_plus and K_minus traces are reproduced from supplied spin-connection components",
            "Minkowski membrane balance equation is explicit",
        ],
        "still_open_primitives": [
            "previous numerical stability witness used T_memb=30 and is not Minkowski-balanced under this equation",
            "recompute all stability witnesses with T_memb=6 or state T_memb=30 belongs to a non-Minkowski branch",
        ],
        "prediction_ready": False,
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Cartan Spin Connection And Background",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Extrinsic Curvature",
    ]
    for key, value in payload["extrinsic_curvature"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Background Balance"])
    for key, value in payload["background_balance"].items():
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
