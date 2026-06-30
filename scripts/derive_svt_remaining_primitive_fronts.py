from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import (
        LAMBDA_PHI,
        MHR2,
        MPL2,
        TENSION,
        VEV,
        expr_text,
    )
    from scripts.derive_svt_quadratic_action_variation import GRAD_S
    from scripts.derive_svt_from_tetrad_connection_blocks import EPS, coeff_eps2
    from scripts.derive_svt_tetrad_aether_primitives import background_measure
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import (
        LAMBDA_PHI,
        MHR2,
        MPL2,
        TENSION,
        VEV,
        expr_text,
    )
    from derive_svt_quadratic_action_variation import GRAD_S
    from derive_svt_from_tetrad_connection_blocks import EPS, coeff_eps2
    from derive_svt_tetrad_aether_primitives import background_measure


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_remaining_primitive_fronts.md"
JSON_PATH = REPORT_DIR / "svt_remaining_primitive_fronts.json"

SCALAR_MODE = sp.Symbol("scalar_mode")


def hr_square_root_background() -> sp.Matrix:
    return sp.diag(VEV, 1, 1, 1)


def stable_hr_projector() -> sp.Matrix:
    root = hr_square_root_background()
    identity = sp.eye(4)
    return sp.factor(identity + 3 * root + 3 * root**2)


def hr_temporal_projector_weight() -> sp.Expr:
    return sp.factor(stable_hr_projector()[0, 0])


def hr_projector_gradient_density() -> sp.Expr:
    return (
        -sp.Rational(1, 2)
        * MHR2
        * MPL2
        * background_measure()
        * hr_temporal_projector_weight()
        * (EPS * GRAD_S) ** 2
    )


def induced_boundary_measure() -> sp.Expr:
    return background_measure()


def ghy_israel_induced_gradient_density() -> sp.Expr:
    return -sp.Rational(1, 2) * TENSION * induced_boundary_measure() * (
        EPS * GRAD_S
    ) ** 2


def radion_double_well_potential() -> sp.Expr:
    phi = -VEV + EPS * SCALAR_MODE
    return LAMBDA_PHI * (phi**2 - VEV**2) ** 2


def radion_potential_mass2() -> sp.Expr:
    potential_eps2 = coeff_eps2(radion_double_well_potential())
    return sp.factor(sp.diff(potential_eps2, SCALAR_MODE, 2))


def current_radion_mass_component() -> sp.Expr:
    return 2 * LAMBDA_PHI * VEV**2


def derived_front_coefficients() -> dict[str, sp.Expr]:
    hr_eps2 = coeff_eps2(hr_projector_gradient_density())
    ghy_eps2 = coeff_eps2(ghy_israel_induced_gradient_density())
    return {
        "hr_temporal_projector_weight": hr_temporal_projector_weight(),
        "scalar_beta_hr_projector": sp.factor(-sp.diff(hr_eps2, GRAD_S, 2)),
        "ghy_israel_induced_measure": induced_boundary_measure(),
        "scalar_beta_ghy_israel_induced": sp.factor(-sp.diff(ghy_eps2, GRAD_S, 2)),
        "radion_double_well_mass2": radion_potential_mass2(),
        "current_radion_mass_component": current_radion_mass_component(),
    }


def build_payload() -> dict:
    coefficients = derived_front_coefficients()
    radion_matches_current = (
        sp.simplify(
            coefficients["radion_double_well_mass2"]
            - coefficients["current_radion_mass_component"]
        )
        == 0
    )
    return {
        "artifact": "svt_remaining_primitive_fronts",
        "status": "three_open_fronts_progressed_with_one_normalization_lock_detected",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "fronts": {
            "hr_matrix_branch": {
                "closed": True,
                "scope": "stable beta-line projector on diagonal temporal square-root branch",
                "full_non_diagonal_matrix_variation_closed": False,
            },
            "ghy_israel": {
                "closed": True,
                "scope": "induced boundary measure normalization",
                "full_extrinsic_curvature_jump_closed": False,
            },
            "radion_potential_mass": {
                "closed": False,
                "scope": "double-well Hessian derived; mismatch with current reduced mass convention",
                "mass_normalization_matches_current": radion_matches_current,
            },
        },
        "derived_coefficients": {
            key: expr_text(value) for key, value in coefficients.items()
        },
        "radion_mass_difference": expr_text(
            sp.factor(
                coefficients["radion_double_well_mass2"]
                - coefficients["current_radion_mass_component"]
            )
        ),
        "closed_primitives": [
            "HR stable beta-line temporal projector weight",
            "Sigma induced-measure contribution to scalar gradient coefficient",
        ],
        "still_open_primitives": [
            "full HR square-root non-diagonal variation",
            "full GHY/Israel extrinsic-curvature jump normalization",
            "radion mass normalization between double-well potential Hessian and reduced SVT coefficient",
        ],
        "prediction_ready": False,
        "next_step": "fix the radion mass normalization convention before replacing conditional scalar mass coefficients",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Remaining Primitive Fronts",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Derived Coefficients",
    ]
    for key, value in payload["derived_coefficients"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            f"Radion mass difference: `{payload['radion_mass_difference']}`",
            "",
            "## Still Open",
        ]
    )
    lines.extend(f"- {item}" for item in payload["still_open_primitives"])
    lines.append(f"Next step: `{payload['next_step']}`")
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
