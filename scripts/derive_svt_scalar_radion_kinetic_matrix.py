from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import MPL2, VEV, expr_text
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import MPL2, VEV, expr_text


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_scalar_radion_kinetic_matrix.md"
JSON_PATH = REPORT_DIR / "svt_scalar_radion_kinetic_matrix.json"

ALPHA_SCALAR_EXACT = sp.Symbol("alpha_scalar_exact_k")


def mixed_radion_kinetic_load() -> sp.Expr:
    return sp.factor(3 * MPL2 / sp.sqrt(VEV))


def exact_reduced_kinetic_matrix() -> sp.Matrix:
    return sp.Matrix(
        [
            [sp.factor(2 * ALPHA_SCALAR_EXACT), mixed_radion_kinetic_load()],
            [mixed_radion_kinetic_load(), sp.Integer(1)],
        ]
    )


def supplied_low_order_kinetic_matrix() -> sp.Matrix:
    return sp.Matrix(
        [
            [
                -6 * MPL2 * (1 + VEV ** -4),
                mixed_radion_kinetic_load(),
            ],
            [mixed_radion_kinetic_load(), sp.Integer(1)],
        ]
    )


def matrix_diagnostics(matrix: sp.Matrix) -> dict[str, sp.Expr | bool]:
    det = sp.factor(matrix.det())
    trace = sp.factor(sp.trace(matrix))
    leading_minor = sp.factor(matrix[0, 0])
    second_minor = sp.factor(matrix[1, 1])
    return {
        "k11": leading_minor,
        "k22": second_minor,
        "determinant": det,
        "trace": trace,
        "positive_definite_by_sylvester": False,
        "indefinite_if_det_negative": True,
    }


def build_payload() -> dict:
    exact_matrix = exact_reduced_kinetic_matrix()
    supplied_matrix = supplied_low_order_kinetic_matrix()
    exact_diag = matrix_diagnostics(exact_matrix)
    supplied_diag = matrix_diagnostics(supplied_matrix)
    return {
        "artifact": "svt_scalar_radion_kinetic_matrix",
        "status": "radion_mixing_included_but_two_field_no_ghost_not_closed",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "basis": ["psi_plus", "chi"],
        "radion": {
            "canonical_field": "chi = deltaPhi/sqrt(v)",
            "kinetic_entry": "1",
            "mixing_entry": expr_text(mixed_radion_kinetic_load()),
        },
        "exact_reduced_matrix": [
            [expr_text(exact_matrix[row, col]) for col in range(2)]
            for row in range(2)
        ],
        "exact_diagnostics": {
            key: (expr_text(value) if isinstance(value, sp.Expr) else value)
            for key, value in exact_diag.items()
        },
        "supplied_low_order_matrix": [
            [expr_text(supplied_matrix[row, col]) for col in range(2)]
            for row in range(2)
        ],
        "supplied_low_order_diagnostics": {
            key: (expr_text(value) if isinstance(value, sp.Expr) else value)
            for key, value in supplied_diag.items()
        },
        "verdict": {
            "positive_eigenvalue_exists": True,
            "negative_eigenvalue_also_exists_if_det_negative": True,
            "full_two_field_no_ghost_proved": False,
            "needs_constraint_or_extra_scalar_sector": True,
        },
        "prediction_ready": False,
        "still_open_primitives": [
            "derive a constraint that removes the negative scalar combination, or",
            "include the Aether scalar deltaA0 and show the full 3x3 kinetic matrix has the required physical signature after constraints",
            "verify sign convention of the supplied EH scalar quadratic action from Cartan expansion",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Scalar Radion Kinetic Matrix",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Exact Diagnostics",
    ]
    for key, value in payload["exact_diagnostics"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Supplied Low-Order Diagnostics"])
    for key, value in payload["supplied_low_order_diagnostics"].items():
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
