from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import MPL2, VEV, expr_text
    from scripts.derive_svt_scalar_radion_kinetic_matrix import (
        mixed_radion_kinetic_load,
        supplied_low_order_kinetic_matrix,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import MPL2, VEV, expr_text
    from derive_svt_scalar_radion_kinetic_matrix import (
        mixed_radion_kinetic_load,
        supplied_low_order_kinetic_matrix,
    )


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_scalar_aether_constraint_check.md"
JSON_PATH = REPORT_DIR / "svt_scalar_aether_constraint_check.json"

C1, C2 = sp.symbols("C1 C2")


def aether_hessian_positive_maxwell() -> sp.Expr:
    return VEV


def aether_hessian_cartan_candidate() -> sp.Expr:
    return -VEV


def cartan_candidate_couplings() -> tuple[sp.Expr, sp.Expr]:
    return (
        -2 * MPL2 / VEV**2,
        -2 * MPL2 / VEV ** sp.Rational(3, 2),
    )


def three_by_three_kinetic_matrix() -> sp.Matrix:
    base = supplied_low_order_kinetic_matrix()
    h_aa = aether_hessian_positive_maxwell()
    return sp.Matrix(
        [
            [base[0, 0], base[0, 1], C1],
            [base[1, 0], base[1, 1], C2],
            [C1, C2, h_aa],
        ]
    )


def schur_reduced_matrix(
    c1: sp.Expr = C1,
    c2: sp.Expr = C2,
    h_aa: sp.Expr | None = None,
) -> sp.Matrix:
    base = supplied_low_order_kinetic_matrix()
    coupling = sp.Matrix([[c1], [c2]])
    hessian = aether_hessian_positive_maxwell() if h_aa is None else h_aa
    return sp.factor(base - coupling * coupling.T / hessian)


def no_cross_reduced_matrix() -> sp.Matrix:
    return schur_reduced_matrix().subs({C1: 0, C2: 0})


def cartan_candidate_reduced_matrix() -> sp.Matrix:
    c1, c2 = cartan_candidate_couplings()
    return schur_reduced_matrix(c1, c2, aether_hessian_cartan_candidate())


def two_by_two_diagnostics(matrix: sp.Matrix) -> dict[str, sp.Expr]:
    return {
        "k11": sp.factor(matrix[0, 0]),
        "k22": sp.factor(matrix[1, 1]),
        "determinant": sp.factor(matrix.det()),
    }


def build_payload() -> dict:
    reduced = schur_reduced_matrix()
    no_cross = no_cross_reduced_matrix()
    cartan = cartan_candidate_reduced_matrix()
    cartan_diag = two_by_two_diagnostics(cartan)
    witness = {MPL2: 4, VEV: 1}
    return {
        "artifact": "svt_scalar_aether_constraint_check",
        "status": "aether_A0_constraint_does_not_close_no_ghost_with_supplied_terms",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "basis_3x3": ["psi_plus", "chi", "deltaA0"],
        "aether_input": {
            "gauge": "deltaA_i = 0",
            "quadratic_term": "v*k^2*deltaA0^2/2",
            "time_derivative_of_deltaA0": False,
            "provided_velocity_cross_terms": False,
        },
        "three_by_three_kinetic_matrix": [
            [expr_text(three_by_three_kinetic_matrix()[row, col]) for col in range(3)]
            for row in range(3)
        ],
        "schur_reduced_2x2": [
            [expr_text(reduced[row, col]) for col in range(2)]
            for row in range(2)
        ],
        "no_cross_reduced_2x2": [
            [expr_text(no_cross[row, col]) for col in range(2)]
            for row in range(2)
        ],
        "diagnostics": {
            "mixing_entry": expr_text(mixed_radion_kinetic_load()),
            "K11_after_elimination": expr_text(reduced[0, 0]),
            "K11_after_elimination_is_more_negative_for_positive_v": True,
            "schur_correction_sign_for_positive_HAA": "negative_semidefinite",
            "full_no_ghost_proved": False,
        },
        "cartan_candidate": {
            "H_AA": expr_text(aether_hessian_cartan_candidate()),
            "C1": expr_text(cartan_candidate_couplings()[0]),
            "C2": expr_text(cartan_candidate_couplings()[1]),
            "reduced_2x2": [
                [expr_text(cartan[row, col]) for col in range(2)]
                for row in range(2)
            ],
            "diagnostics": {
                key: expr_text(value) for key, value in cartan_diag.items()
            },
            "sample_Mpl2_4_v_1": {
                key: expr_text(value.subs(witness)) for key, value in cartan_diag.items()
            },
            "sample_positive_definite": bool(
                cartan_diag["k11"].subs(witness) > 0
                and cartan_diag["determinant"].subs(witness) > 0
            ),
        },
        "verdict": {
            "deltaA0_is_nondynamical": True,
            "provided_F2_term_alone_decouples_when_C1_C2_zero": True,
            "generic_positive_HAA_constraint_cannot_fix_negative_K11": True,
            "requires_missing_cross_terms_or_opposite_sign_HAA": True,
            "cartan_candidate_closes_witness_Mpl2_4_v_1": bool(
                cartan_diag["k11"].subs(witness) > 0
                and cartan_diag["determinant"].subs(witness) > 0
            ),
        },
        "prediction_ready": False,
        "needed_inputs": [
            "explicit C1 and C2 velocity-cross couplings from Cartan/Aether expansion, if they exist",
            "proof that H_AA has the sign needed without creating an Aether ghost",
            "or an independent constraint that removes the negative trace combination before kinetic-sign testing",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Scalar Aether Constraint Check",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Diagnostics",
    ]
    for key, value in payload["diagnostics"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Cartan Candidate"])
    for key, value in payload["cartan_candidate"]["diagnostics"].items():
        lines.append(f"- {key}: `{value}`")
    lines.append(
        f"- sample_Mpl2_4_v_1: `{payload['cartan_candidate']['sample_Mpl2_4_v_1']}`"
    )
    lines.append(
        f"- sample_positive_definite: `{payload['cartan_candidate']['sample_positive_definite']}`"
    )
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
