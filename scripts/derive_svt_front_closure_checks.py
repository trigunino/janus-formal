from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import (
        LAMBDA_PHI,
        MPL2,
        VEV,
        expr_text,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import (
        LAMBDA_PHI,
        MPL2,
        VEV,
        expr_text,
    )


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_front_closure_checks.md"
JSON_PATH = REPORT_DIR / "svt_front_closure_checks.json"

H00, H01, H02, H03, H11, H12, H13, H22, H23, H33 = sp.symbols(
    "h00 h01 h02 h03 h11 h12 h13 h22 h23 h33"
)
RADION_MODE, CANONICAL_MODE = sp.symbols("radion_mode canonical_mode")
SURFACE_TRACE = sp.Symbol("S_trace")


def hr_background_sqrt_eigenvalues() -> list[sp.Expr]:
    return [VEV, sp.Integer(1), sp.Integer(1), sp.Integer(1)]


def hr_metric_perturbation() -> sp.Matrix:
    return sp.Matrix(
        [
            [H00, H01, H02, H03],
            [H01, H11, H12, H13],
            [H02, H12, H22, H23],
            [H03, H13, H23, H33],
        ]
    )


def hr_sqrt_frechet_variation() -> sp.Matrix:
    eig = hr_background_sqrt_eigenvalues()
    perturbation = hr_metric_perturbation()
    return sp.Matrix(
        4,
        4,
        lambda i, j: sp.factor(perturbation[i, j] / (eig[i] + eig[j])),
    )


def hr_sylvester_residual() -> sp.Matrix:
    sqrt0 = sp.diag(*hr_background_sqrt_eigenvalues())
    delta_sqrt = hr_sqrt_frechet_variation()
    return sp.simplify(sqrt0 * delta_sqrt + delta_sqrt * sqrt0 - hr_metric_perturbation())


def stable_hr_projector_variation() -> sp.Matrix:
    sqrt0 = sp.diag(*hr_background_sqrt_eigenvalues())
    delta_sqrt = hr_sqrt_frechet_variation()
    delta_metric = hr_metric_perturbation()
    return sp.simplify(3 * delta_sqrt + 3 * delta_metric)


def hr_componentwise_projector_loads() -> dict[str, sp.Expr]:
    variation = stable_hr_projector_variation()
    return {
        "temporal_diagonal_load": sp.factor(variation[0, 0] / H00),
        "time_space_offdiag_load": sp.factor(variation[0, 1] / H01),
        "spatial_offdiag_load": sp.factor(variation[1, 2] / H12),
        "spatial_diagonal_load": sp.factor(variation[1, 1] / H11),
    }


def hr_scalar_projector_weight() -> sp.Expr:
    return sp.factor(1 + 3 * VEV + 3 * VEV**2)


def israel_jump_trace() -> sp.Expr:
    return sp.factor(-SURFACE_TRACE / (2 * MPL2))


def israel_jump_tensor_component(surface_component: sp.Expr, induced_component: sp.Expr) -> sp.Expr:
    return sp.factor((surface_component - sp.Rational(1, 2) * induced_component * SURFACE_TRACE) / MPL2)


def israel_pure_tension_component() -> sp.Expr:
    tension = sp.Symbol("T_memb")
    induced_component = sp.Symbol("h_ab")
    surface_component = -tension * induced_component
    trace = -3 * tension
    return sp.factor(
        israel_jump_tensor_component(surface_component, induced_component).subs(
            SURFACE_TRACE, trace
        )
    )


def radion_mass_from_double_well(prefactor: sp.Expr = sp.Integer(1)) -> sp.Expr:
    phi = -VEV + RADION_MODE
    potential = prefactor * LAMBDA_PHI * (phi**2 - VEV**2) ** 2
    return sp.factor(sp.diff(potential, RADION_MODE, 2).subs(RADION_MODE, 0))


def radion_mass_after_canonical_rescale(scale: sp.Expr) -> sp.Expr:
    phi = -VEV + CANONICAL_MODE / scale
    potential = LAMBDA_PHI * (phi**2 - VEV**2) ** 2
    return sp.factor(sp.diff(potential, CANONICAL_MODE, 2).subs(CANONICAL_MODE, 0))


def build_payload() -> dict:
    residual = hr_sylvester_residual()
    loads = hr_componentwise_projector_loads()
    full_mass = radion_mass_from_double_well()
    quarter_mass = radion_mass_from_double_well(sp.Rational(1, 4))
    rescaled_mass = radion_mass_after_canonical_rescale(sp.Integer(2))
    reduced_mass = 2 * LAMBDA_PHI * VEV**2
    return {
        "artifact": "svt_front_closure_checks",
        "status": "israel_closed_hr_frechet_closed_radion_convention_required",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "hr_non_diagonal": {
            "sqrt_frechet_closed": residual == sp.zeros(4),
            "sylvester_residual_zero": str(residual),
            "componentwise_projector_loads": {
                key: expr_text(value) for key, value in loads.items()
            },
            "scalar_projector_weight": expr_text(hr_scalar_projector_weight()),
            "scalar_weight_valid_for_all_components": False,
            "requires_componentwise_svt_projection": True,
        },
        "israel_jump": {
            "trace_jump": expr_text(israel_jump_trace()),
            "tensor_jump_formula": "(S_ab - h_ab*S_trace/2)/Mpl2",
            "pure_tension_jump_component": expr_text(israel_pure_tension_component()),
            "algebraic_jump_closed": True,
            "boundary_source_selection_closed": False,
        },
        "radion_normalization": {
            "double_well_prefactor_1_mass2": expr_text(full_mass),
            "double_well_prefactor_1_over_4_mass2": expr_text(quarter_mass),
            "canonical_rescale_chi_equals_2_delta_phi_mass2": expr_text(rescaled_mass),
            "current_reduced_mass2": expr_text(reduced_mass),
            "prefactor_1_matches_current": sp.simplify(full_mass - reduced_mass) == 0,
            "prefactor_1_over_4_matches_current": sp.simplify(quarter_mass - reduced_mass) == 0,
            "rescale_2_matches_current": sp.simplify(rescaled_mass - reduced_mass) == 0,
        },
        "closed_primitives": [
            "first-order HR square-root Frechet/Sylvester map for non-diagonal perturbations",
            "trace-reversed Israel jump algebra in three boundary dimensions",
        ],
        "still_open_primitives": [
            "second-order HR potential Hessian projected into full SVT sectors",
            "Janus/source selection of boundary stress, not only Israel algebra",
            "choice of radion potential prefactor or canonical field normalization",
        ],
        "prediction_ready": False,
        "next_step": "use the HR Frechet map to build the second-order HR Hessian in SVT variables, then choose and propagate one radion normalization convention",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Front Closure Checks",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## HR Component Loads",
    ]
    for key, value in payload["hr_non_diagonal"]["componentwise_projector_loads"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Israel Jump",
            f"- trace_jump: `{payload['israel_jump']['trace_jump']}`",
            f"- pure_tension_jump_component: `{payload['israel_jump']['pure_tension_jump_component']}`",
            "",
            "## Radion Normalization",
        ]
    )
    for key, value in payload["radion_normalization"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Still Open"])
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
