from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import MPL2, VEV, expr_text
    from scripts.derive_svt_scalar_aether_constraint_check import (
        cartan_candidate_reduced_matrix,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import MPL2, VEV, expr_text
    from derive_svt_scalar_aether_constraint_check import cartan_candidate_reduced_matrix


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_scalar_canonical_basis_check.md"
JSON_PATH = REPORT_DIR / "svt_scalar_canonical_basis_check.json"


def proposed_basis_jacobian() -> sp.Matrix:
    # psi_old = psi_tilde + chi/(2*sqrt(v)*Mpl2), chi_old = chi.
    return sp.Matrix(
        [
            [1, 1 / (2 * sp.sqrt(VEV) * MPL2)],
            [0, 1],
        ]
    )


def transformed_matrix() -> sp.Matrix:
    jacobian = proposed_basis_jacobian()
    return sp.factor(jacobian.T * cartan_candidate_reduced_matrix() * jacobian)


def exact_diagonalizing_shift() -> sp.Expr:
    matrix = cartan_candidate_reduced_matrix()
    return sp.factor(-matrix[0, 1] / matrix[0, 0])


def constraint_vector() -> sp.Matrix:
    # chi = 2*sqrt(v)*Mpl2*psi.
    return sp.Matrix([1, 2 * sp.sqrt(VEV) * MPL2])


def constrained_single_mode_alpha() -> sp.Expr:
    vector = constraint_vector()
    return sp.factor((vector.T * cartan_candidate_reduced_matrix() * vector)[0])


def diagnostics(matrix: sp.Matrix) -> dict[str, sp.Expr]:
    return {
        "k11": sp.factor(matrix[0, 0]),
        "k12": sp.factor(matrix[0, 1]),
        "k22": sp.factor(matrix[1, 1]),
        "determinant": sp.factor(matrix.det()),
    }


def build_payload() -> dict:
    original = cartan_candidate_reduced_matrix()
    transformed = transformed_matrix()
    witness = {MPL2: 4, VEV: 1}
    original_diag = diagnostics(original)
    transformed_diag = diagnostics(transformed)
    constrained_alpha = constrained_single_mode_alpha()
    return {
        "artifact": "svt_scalar_canonical_basis_check",
        "status": "basis_change_preserves_ghost_constraint_projection_is_conditional",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "proposed_basis_change": "psi_p = tilde_psi_p + chi/(2*sqrt(v)*Mpl2)",
        "basis_change_jacobian_det": expr_text(proposed_basis_jacobian().det()),
        "original_diagnostics": {
            key: expr_text(value) for key, value in original_diag.items()
        },
        "transformed_diagnostics": {
            key: expr_text(value) for key, value in transformed_diag.items()
        },
        "exact_diagonalizing_shift": expr_text(exact_diagonalizing_shift()),
        "cartan_constraint_projection": {
            "constraint": "chi = 2*sqrt(v)*Mpl2*psi_p",
            "single_mode_alpha": expr_text(constrained_alpha),
            "sample_Mpl2_4_v_1_alpha": expr_text(constrained_alpha.subs(witness)),
            "conditional_positive_on_sample": bool(constrained_alpha.subs(witness) > 0),
        },
        "sample_Mpl2_4_v_1": {
            "original": {
                key: expr_text(value.subs(witness))
                for key, value in original_diag.items()
            },
            "transformed": {
                key: expr_text(value.subs(witness))
                for key, value in transformed_diag.items()
            },
        },
        "verdict": {
            "invertible_basis_change_can_change_determinant_sign": False,
            "proposed_basis_change_closes_no_ghost": False,
            "constraint_projection_gives_positive_sample_mode": bool(
                constrained_alpha.subs(witness) > 0
            ),
            "constraint_projection_is_new_axiom_until_derived": True,
            "prediction_ready": False,
        },
        "needed_inputs": [
            "derivation of chi = 2*sqrt(v)*Mpl2*psi_p from Cartan-Janus boundary equations",
            "or a non-invertible constraint from the full variational principle eliminating one scalar mode",
            "otherwise the negative eigenvalue remains physical in the unconstrained two-field kinetic matrix",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Scalar Canonical Basis Check",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['verdict']['prediction_ready']}`",
        "",
        "## Basis Change",
    ]
    for key, value in payload["transformed_diagnostics"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Constraint Projection"])
    for key, value in payload["cartan_constraint_projection"].items():
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
