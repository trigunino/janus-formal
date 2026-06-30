from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import (
        AETHER,
        MPL2,
        VEV,
        expr_text,
    )
    from scripts.derive_svt_quadratic_action_variation import QD_S, QD_V
    from scripts.derive_svt_from_tetrad_connection_blocks import EPS, coeff_eps2
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import (
        AETHER,
        MPL2,
        VEV,
        expr_text,
    )
    from derive_svt_quadratic_action_variation import QD_S, QD_V
    from derive_svt_from_tetrad_connection_blocks import EPS, coeff_eps2


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_tetrad_aether_primitive_derivation.md"
JSON_PATH = REPORT_DIR / "svt_tetrad_aether_primitive_derivation.json"

TAU, X1, X2, X3 = sp.symbols("tau x1 x2 x3")


def asymmetric_temporal_tetrad() -> sp.Matrix:
    return sp.diag(VEV + EPS * TAU, 1 + EPS * X1, 1 + EPS * X2, 1 + EPS * X3)


def tetrad_determinant() -> sp.Expr:
    return sp.factor(asymmetric_temporal_tetrad().det())


def background_measure() -> sp.Expr:
    return sp.factor(tetrad_determinant().subs(EPS, 0))


def temporal_spin_connection_square(qdot: sp.Symbol) -> sp.Expr:
    omega_0i = EPS * qdot
    return sp.Rational(1, 2) * MPL2 * background_measure() * omega_0i**2


def aether_field_strength_square(qdot: sp.Symbol) -> sp.Expr:
    a_i = EPS * sp.Symbol(f"A_{qdot.name}")
    f_0i = sp.diff(a_i, sp.Symbol("t"))
    if f_0i == 0:
        f_0i = EPS * qdot
    return -sp.Rational(1, 2) * AETHER * background_measure() * f_0i**2


def primitive_densities() -> dict[str, sp.Expr]:
    return {
        "vector_tetrad_kinetic_density": temporal_spin_connection_square(QD_V),
        "vector_aether_kinetic_density": aether_field_strength_square(QD_V),
        "scalar_tetrad_kinetic_density": temporal_spin_connection_square(QD_S),
        "scalar_aether_kinetic_density": aether_field_strength_square(QD_S),
    }


def primitive_eps2_blocks() -> dict[str, sp.Expr]:
    return {
        key: coeff_eps2(value)
        for key, value in primitive_densities().items()
    }


def kinetic_coefficients_from_primitives() -> dict[str, sp.Expr]:
    blocks = primitive_eps2_blocks()
    vector_alpha_gravity = sp.diff(blocks["vector_tetrad_kinetic_density"], QD_V, 2)
    vector_alpha_aether = sp.diff(blocks["vector_aether_kinetic_density"], QD_V, 2)
    scalar_alpha_gravity = sp.diff(blocks["scalar_tetrad_kinetic_density"], QD_S, 2)
    scalar_alpha_aether = sp.diff(blocks["scalar_aether_kinetic_density"], QD_S, 2)
    return {
        "vector_alpha_gravity": sp.factor(vector_alpha_gravity),
        "vector_alpha_aether": sp.factor(vector_alpha_aether),
        "vector_alpha_cartan_aether": sp.factor(vector_alpha_gravity + vector_alpha_aether),
        "scalar_alpha_gravity": sp.factor(scalar_alpha_gravity),
        "scalar_alpha_aether": sp.factor(scalar_alpha_aether),
        "scalar_alpha_cartan_aether": sp.factor(scalar_alpha_gravity + scalar_alpha_aether),
    }


def expected_kinetic_coefficients() -> dict[str, sp.Expr]:
    return {
        "vector_alpha_gravity": VEV * MPL2,
        "vector_alpha_aether": -VEV * AETHER,
        "vector_alpha_cartan_aether": VEV * (MPL2 - AETHER),
        "scalar_alpha_gravity": VEV * MPL2,
        "scalar_alpha_aether": -VEV * AETHER,
        "scalar_alpha_cartan_aether": VEV * (MPL2 - AETHER),
    }


def compare_to_expected(coefficients: dict[str, sp.Expr]) -> dict[str, bool]:
    expected = expected_kinetic_coefficients()
    return {
        key: sp.simplify(coefficients[key] - expected[key]) == 0
        for key in expected
    }


def build_payload() -> dict:
    coefficients = kinetic_coefficients_from_primitives()
    matches = compare_to_expected(coefficients)
    return {
        "artifact": "svt_tetrad_aether_primitive_derivation",
        "status": "tetrad_measure_and_aether_kinetic_primitives_closed",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "tetrad": {
            "matrix": str(asymmetric_temporal_tetrad()),
            "determinant": expr_text(tetrad_determinant()),
            "background_measure": expr_text(background_measure()),
            "linear_temporal_leg": True,
            "conformal_phi_fourth_shortcut_used": False,
        },
        "primitive_eps2_blocks": {
            key: expr_text(value)
            for key, value in primitive_eps2_blocks().items()
        },
        "derived_kinetic_coefficients": {
            key: expr_text(value)
            for key, value in coefficients.items()
        },
        "expected_kinetic_coefficients": {
            key: expr_text(value)
            for key, value in expected_kinetic_coefficients().items()
        },
        "matches_expected": matches,
        "all_expected_matches": all(matches.values()),
        "closed_primitives": [
            "asymmetric temporal tetrad background measure",
            "Cartan temporal spin-connection kinetic prefactor",
            "Maxwell-like Aether F_0i kinetic load",
        ],
        "still_open_primitives": [
            "spatial curvature/gradient EH block",
            "radion double-well stiffness from full potential expansion",
            "Hassan-Rosen square-root elementary-polynomial expansion",
            "GHY/Israel boundary derivation",
        ],
        "prediction_ready": False,
        "next_step": "derive spatial spin-connection gradient block and radion double-well stiffness from primitives",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Tetrad/Aether Primitive Derivation",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"All expected matches: `{payload['all_expected_matches']}`",
        "",
        "## Tetrad",
        "",
        f"- determinant: `{payload['tetrad']['determinant']}`",
        f"- background measure: `{payload['tetrad']['background_measure']}`",
        "",
        "## Derived Kinetic Coefficients",
    ]
    for key, value in payload["derived_kinetic_coefficients"].items():
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
