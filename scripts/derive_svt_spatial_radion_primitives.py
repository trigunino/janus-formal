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
    from scripts.derive_svt_quadratic_action_variation import GRAD_S, GRAD_V, QD_S
    from scripts.derive_svt_from_tetrad_connection_blocks import EPS, coeff_eps2
    from scripts.derive_svt_tetrad_aether_primitives import background_measure
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import (
        LAMBDA_PHI,
        MPL2,
        VEV,
        expr_text,
    )
    from derive_svt_quadratic_action_variation import GRAD_S, GRAD_V, QD_S
    from derive_svt_from_tetrad_connection_blocks import EPS, coeff_eps2
    from derive_svt_tetrad_aether_primitives import background_measure


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_spatial_radion_primitive_derivation.md"
JSON_PATH = REPORT_DIR / "svt_spatial_radion_primitive_derivation.json"

RADION_FLUCT = sp.symbols("radion_fluct")


def spatial_spin_connection_density(gradient: sp.Symbol) -> sp.Expr:
    omega_ij = EPS * gradient
    return -sp.Rational(1, 2) * MPL2 * background_measure() * omega_ij**2


def radion_stiffness_profile() -> sp.Expr:
    phi = -VEV + EPS * RADION_FLUCT
    return sp.factor(2 * LAMBDA_PHI * phi**2)


def radion_kinetic_density() -> sp.Expr:
    stiffness_at_background = radion_stiffness_profile().subs(EPS, 0)
    return sp.Rational(1, 2) * stiffness_at_background * (EPS * QD_S) ** 2


def primitive_densities() -> dict[str, sp.Expr]:
    return {
        "vector_spatial_spin_connection_density": spatial_spin_connection_density(GRAD_V),
        "scalar_spatial_spin_connection_density": spatial_spin_connection_density(GRAD_S),
        "scalar_radion_stiffness_density": radion_kinetic_density(),
    }


def primitive_eps2_blocks() -> dict[str, sp.Expr]:
    return {
        key: coeff_eps2(value)
        for key, value in primitive_densities().items()
    }


def derived_coefficients() -> dict[str, sp.Expr]:
    blocks = primitive_eps2_blocks()
    vector_beta_gravity = -sp.diff(
        blocks["vector_spatial_spin_connection_density"], GRAD_V, 2
    )
    scalar_beta_gravity = -sp.diff(
        blocks["scalar_spatial_spin_connection_density"], GRAD_S, 2
    )
    scalar_alpha_radion = sp.diff(
        blocks["scalar_radion_stiffness_density"], QD_S, 2
    )
    return {
        "vector_beta_gravity": sp.factor(vector_beta_gravity),
        "scalar_beta_gravity": sp.factor(scalar_beta_gravity),
        "scalar_alpha_radion": sp.factor(scalar_alpha_radion),
    }


def expected_coefficients() -> dict[str, sp.Expr]:
    return {
        "vector_beta_gravity": MPL2 * VEV,
        "scalar_beta_gravity": MPL2 * VEV,
        "scalar_alpha_radion": 2 * LAMBDA_PHI * VEV**2,
    }


def compare_to_expected(coefficients: dict[str, sp.Expr]) -> dict[str, bool]:
    expected = expected_coefficients()
    return {
        key: sp.simplify(coefficients[key] - expected[key]) == 0
        for key in expected
    }


def build_payload() -> dict:
    coefficients = derived_coefficients()
    matches = compare_to_expected(coefficients)
    return {
        "artifact": "svt_spatial_radion_primitive_derivation",
        "status": "spatial_gradient_and_radion_stiffness_primitives_closed",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "background_measure": expr_text(background_measure()),
        "radion_stiffness_profile": expr_text(radion_stiffness_profile()),
        "radion_stiffness_at_background": expr_text(
            radion_stiffness_profile().subs(EPS, 0)
        ),
        "primitive_eps2_blocks": {
            key: expr_text(value)
            for key, value in primitive_eps2_blocks().items()
        },
        "derived_coefficients": {
            key: expr_text(value)
            for key, value in coefficients.items()
        },
        "expected_coefficients": {
            key: expr_text(value)
            for key, value in expected_coefficients().items()
        },
        "matches_expected": matches,
        "all_expected_matches": all(matches.values()),
        "closed_primitives": [
            "Cartan spatial spin-connection gradient prefactor",
            "radion local field-space stiffness at Phi=-v",
        ],
        "still_open_primitives": [
            "Hassan-Rosen square-root elementary-polynomial expansion",
            "membrane gradient/boundary normalization from GHY/Israel",
            "radion potential mass term separated from kinetic stiffness",
        ],
        "prediction_ready": False,
        "next_step": "derive Hassan-Rosen square-root and membrane/Israel gradient terms",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Spatial/Radion Primitive Derivation",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"All expected matches: `{payload['all_expected_matches']}`",
        "",
        "## Derived Coefficients",
    ]
    for key, value in payload["derived_coefficients"].items():
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
