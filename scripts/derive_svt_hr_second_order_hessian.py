from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import VEV, expr_text
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import VEV, expr_text


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_hr_second_order_hessian.md"
JSON_PATH = REPORT_DIR / "svt_hr_second_order_hessian.json"

EPS = sp.Symbol("eps")
TENSOR, VECTOR, LAPSE, SPATIAL = sp.symbols("tensor vector lapse spatial")


def background_sqrt() -> sp.Matrix:
    return sp.diag(VEV, 1, 1, 1)


def sqrt_expansion_for(delta_metric: sp.Matrix) -> sp.Matrix:
    eigenvalues = [VEV, sp.Integer(1), sp.Integer(1), sp.Integer(1)]
    x1 = sp.Matrix(
        4,
        4,
        lambda i, j: sp.factor(delta_metric[i, j] / (eigenvalues[i] + eigenvalues[j])),
    )
    x2_source = sp.simplify(x1 * x1)
    x2 = sp.Matrix(
        4,
        4,
        lambda i, j: sp.factor(-x2_source[i, j] / (eigenvalues[i] + eigenvalues[j])),
    )
    return background_sqrt() + EPS * x1 + EPS**2 * x2


def sqrt_residual_coefficients(delta_metric: sp.Matrix) -> dict[str, sp.Matrix]:
    sqrt_series = sqrt_expansion_for(delta_metric)
    target = background_sqrt() ** 2 + EPS * delta_metric
    residual = sp.expand(sqrt_series * sqrt_series - target)
    return {
        "eps1": residual.applyfunc(lambda entry: sp.factor(entry.coeff(EPS, 1))),
        "eps2": residual.applyfunc(lambda entry: sp.factor(entry.coeff(EPS, 2))),
    }


def residual_vanishes_through_second_order(delta_metric: sp.Matrix) -> bool:
    coefficients = sqrt_residual_coefficients(delta_metric)
    zero = sp.zeros(4)
    return coefficients["eps1"] == zero and coefficients["eps2"] == zero


def elementary_polynomials(matrix: sp.Matrix) -> dict[str, sp.Expr]:
    tr1 = sp.trace(matrix)
    tr2 = sp.trace(matrix**2)
    tr3 = sp.trace(matrix**3)
    tr4 = sp.trace(matrix**4)
    return {
        "e1": sp.factor(tr1),
        "e2": sp.factor((tr1**2 - tr2) / 2),
        "e3": sp.factor((tr1**3 - 3 * tr1 * tr2 + 2 * tr3) / 6),
        "e4": sp.factor(
            (tr1**4 - 6 * tr1**2 * tr2 + 3 * tr2**2 + 8 * tr1 * tr3 - 6 * tr4)
            / 24
        ),
    }


def stable_hr_potential(matrix: sp.Matrix) -> sp.Expr:
    polynomials = elementary_polynomials(matrix)
    return sp.factor(
        polynomials["e1"]
        + 3 * polynomials["e2"]
        + 3 * polynomials["e3"]
        + polynomials["e4"]
    )


def eps2_coefficient(expr: sp.Expr) -> sp.Expr:
    return sp.factor(sp.expand(expr).coeff(EPS, 2))


def potential_eps2_for(delta_metric: sp.Matrix) -> sp.Expr:
    return eps2_coefficient(stable_hr_potential(sqrt_expansion_for(delta_metric)))


def tensor_metric_perturbation() -> sp.Matrix:
    return sp.Matrix(
        [
            [0, 0, 0, 0],
            [0, 0, TENSOR, 0],
            [0, TENSOR, 0, 0],
            [0, 0, 0, 0],
        ]
    )


def vector_metric_perturbation() -> sp.Matrix:
    return sp.Matrix(
        [
            [0, VECTOR, 0, 0],
            [VECTOR, 0, 0, 0],
            [0, 0, 0, 0],
            [0, 0, 0, 0],
        ]
    )


def scalar_metric_perturbation() -> sp.Matrix:
    return sp.diag(LAPSE, SPATIAL, SPATIAL, SPATIAL)


def hessian(expr: sp.Expr, variables: list[sp.Symbol]) -> list[list[sp.Expr]]:
    return [
        [sp.factor(sp.diff(expr, row, col)) for col in variables]
        for row in variables
    ]


def derived_hessians() -> dict:
    tensor_eps2 = potential_eps2_for(tensor_metric_perturbation())
    vector_eps2 = potential_eps2_for(vector_metric_perturbation())
    scalar_eps2 = potential_eps2_for(scalar_metric_perturbation())
    scalar_hessian = hessian(scalar_eps2, [LAPSE, SPATIAL])
    return {
        "tensor_eps2": tensor_eps2,
        "tensor_hessian": sp.factor(sp.diff(tensor_eps2, TENSOR, 2)),
        "vector_eps2": vector_eps2,
        "vector_hessian": sp.factor(sp.diff(vector_eps2, VECTOR, 2)),
        "scalar_eps2": scalar_eps2,
        "scalar_hessian": scalar_hessian,
        "scalar_det_hessian": sp.factor(sp.Matrix(scalar_hessian).det()),
    }


def build_payload() -> dict:
    values = derived_hessians()
    residual_checks = {
        "tensor": residual_vanishes_through_second_order(tensor_metric_perturbation()),
        "vector": residual_vanishes_through_second_order(vector_metric_perturbation()),
        "scalar": residual_vanishes_through_second_order(scalar_metric_perturbation()),
    }
    return {
        "artifact": "svt_hr_second_order_hessian",
        "status": "hr_second_order_sqrt_hessian_projected_but_scalar_constraints_open",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "beta_line": {"beta1": 1, "beta2": 3, "beta3": 3, "beta4": 1},
        "sqrt_method": "S=S0+eps*X1+eps^2*X2, S0*X1+X1*S0=H, S0*X2+X2*S0=-X1^2",
        "sqrt_residual_through_eps2": residual_checks,
        "projected_eps2_potentials": {
            "tensor": expr_text(values["tensor_eps2"]),
            "vector": expr_text(values["vector_eps2"]),
            "scalar_lapse_spatial": expr_text(values["scalar_eps2"]),
        },
        "projected_hessians": {
            "tensor": expr_text(values["tensor_hessian"]),
            "vector": expr_text(values["vector_hessian"]),
            "scalar_lapse_spatial": [
                [expr_text(item) for item in row]
                for row in values["scalar_hessian"]
            ],
            "scalar_det": expr_text(values["scalar_det_hessian"]),
        },
        "closure": {
            "sqrt_expansion_verified_through_second_order": all(residual_checks.values()),
            "tensor_projected_hr_hessian_closed": True,
            "vector_projected_hr_hessian_closed": True,
            "scalar_raw_lapse_spatial_hessian_closed": True,
            "scalar_reduced_after_constraints_closed": False,
        },
        "still_open_primitives": [
            "lapse/shift/bending constraint solution selecting scalar reduced variable",
            "multiplication by exact HR membrane normalization/sign convention",
            "matching this HR Hessian to gradient-vs-mass channel in the full SVT action",
        ],
        "prediction_ready": False,
        "needed_inputs": [
            "exact SVT constraint equations for lapse, shift, and boundary bending",
            "sign convention for HR contribution in the action density",
            "whether HR term contributes here as mass, gradient, or both after eliminating constraints",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT HR Second-Order Hessian",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Projected Hessians",
    ]
    for key, value in payload["projected_hessians"].items():
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
