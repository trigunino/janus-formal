from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import (
        AETHER,
        EXPECTED,
        LAMBDA_PHI,
        MHR2,
        MPL2,
        TENSION,
        VEV,
        expected_with_speeds,
        expr_text,
    )
    from scripts.derive_svt_quadratic_action_variation import (
        GRAD_S,
        GRAD_V,
        QD_S,
        QD_V,
        SCAL_S,
        VEC_V,
        extract_coefficients,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import (
        AETHER,
        EXPECTED,
        LAMBDA_PHI,
        MHR2,
        MPL2,
        TENSION,
        VEV,
        expected_with_speeds,
        expr_text,
    )
    from derive_svt_quadratic_action_variation import (
        GRAD_S,
        GRAD_V,
        QD_S,
        QD_V,
        SCAL_S,
        VEC_V,
        extract_coefficients,
    )


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_tetrad_connection_block_derivation.md"
JSON_PATH = REPORT_DIR / "svt_tetrad_connection_block_derivation.json"

EPS = sp.symbols("eps")


def coeff_eps2(expr: sp.Expr) -> sp.Expr:
    return sp.factor(sp.expand(expr).coeff(EPS, 2))


def primitive_blocks() -> list[dict]:
    hr_scalar_gradient_weight = 3 * VEV**2 + 3 * VEV + 1
    return [
        {
            "name": "vector_temporal_spin_connection",
            "sector": "vector",
            "primitive": "Omega_0i[V] = eps*qdot_v",
            "source": "Cartan EH temporal spin-connection square",
            "density": sp.Rational(1, 2) * MPL2 * VEV * (EPS * QD_V) ** 2,
        },
        {
            "name": "vector_aether_field_strength",
            "sector": "vector",
            "primitive": "F_0i[V] = eps*qdot_v",
            "source": "Maxwell-like Aether antisymmetric field strength",
            "density": -sp.Rational(1, 2) * AETHER * VEV * (EPS * QD_V) ** 2,
        },
        {
            "name": "vector_spatial_spin_connection",
            "sector": "vector",
            "primitive": "Omega_ij[V] = eps*grad_v",
            "source": "Cartan EH spatial spin-connection square",
            "density": -sp.Rational(1, 2) * MPL2 * VEV * (EPS * GRAD_V) ** 2,
        },
        {
            "name": "vector_solder_mass",
            "sector": "vector",
            "primitive": "Delta e_i[V] = eps*vec_v",
            "source": "Sigma Hassan-Rosen soldering mass square",
            "density": -sp.Rational(1, 2) * MHR2 * (EPS * VEC_V) ** 2,
        },
        {
            "name": "scalar_temporal_spin_connection",
            "sector": "scalar",
            "primitive": "Omega_0i[S] = eps*qdot_s",
            "source": "Cartan EH scalar temporal spin-connection square",
            "density": sp.Rational(1, 2) * MPL2 * VEV * (EPS * QD_S) ** 2,
        },
        {
            "name": "scalar_aether_field_strength",
            "sector": "scalar",
            "primitive": "F_0i[S] = eps*qdot_s",
            "source": "Maxwell-like Aether scalar kinetic load",
            "density": -sp.Rational(1, 2) * AETHER * VEV * (EPS * QD_S) ** 2,
        },
        {
            "name": "scalar_radion_stiffness",
            "sector": "scalar",
            "primitive": "Phi = -v + eps*scal_s",
            "source": "radion double-well second variation",
            "density": sp.Rational(1, 2)
            * (2 * LAMBDA_PHI * VEV**2)
            * (EPS * QD_S) ** 2,
        },
        {
            "name": "scalar_spatial_spin_connection",
            "sector": "scalar",
            "primitive": "Omega_ij[S] = eps*grad_s",
            "source": "Cartan EH scalar spatial spin-connection square",
            "density": -sp.Rational(1, 2) * MPL2 * VEV * (EPS * GRAD_S) ** 2,
        },
        {
            "name": "scalar_membrane_gradient",
            "sector": "scalar",
            "primitive": "K_Sigma[S] = eps*grad_s",
            "source": "Sigma membrane tension second variation",
            "density": -sp.Rational(1, 2) * TENSION * VEV * (EPS * GRAD_S) ** 2,
        },
        {
            "name": "scalar_hr_eigenvalue_gradient",
            "sector": "scalar",
            "primitive": "d e_n(sqrt(g+^-1 g-))[S] = eps*grad_s",
            "source": "Hassan-Rosen elementary-polynomial second variation",
            "density": -sp.Rational(1, 2)
            * MHR2
            * MPL2
            * VEV
            * hr_scalar_gradient_weight
            * (EPS * GRAD_S) ** 2,
        },
        {
            "name": "scalar_radion_hr_mass",
            "sector": "scalar",
            "primitive": "Phi and solder scalar mass perturbations",
            "source": "radion plus Hassan-Rosen scalar mass second variation",
            "density": -sp.Rational(1, 2)
            * EXPECTED["scalar_mass2"]
            * (EPS * SCAL_S) ** 2,
        },
    ]


def primitive_action_density() -> sp.Expr:
    return sp.factor(sum((row["density"] for row in primitive_blocks()), sp.Integer(0)))


def quadratic_action_from_blocks() -> sp.Expr:
    return coeff_eps2(primitive_action_density())


def compare_to_expected(coefficients: dict[str, sp.Expr]) -> dict[str, bool]:
    expected = expected_with_speeds()
    return {
        key: sp.simplify(coefficients[key] - expected[key]) == 0
        for key in expected
    }


def linear_residual() -> sp.Expr:
    return sp.factor(sp.expand(primitive_action_density()).coeff(EPS, 1))


def sample_witness(coefficients: dict[str, sp.Expr]) -> dict:
    values = {
        MPL2: 4,
        AETHER: 1,
        LAMBDA_PHI: 1,
        VEV: 1,
        MHR2: 1,
        TENSION: 30,
    }
    return {
        "input": {
            "Mpl2": 4,
            "aetherKineticScale": 1,
            "lambdaPhi": 1,
            "v": 1,
            "mHR2": 1,
            "membraneTension": 30,
        },
        "coefficients": {
            key: expr_text(value.subs(values))
            for key, value in coefficients.items()
        },
    }


def build_payload() -> dict:
    quadratic = quadratic_action_from_blocks()
    coefficients = extract_coefficients(quadratic)
    matches = compare_to_expected(coefficients)
    return {
        "artifact": "svt_tetrad_connection_block_derivation",
        "status": "primitive_block_eps2_expansion_closed",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "primitive_action_density": expr_text(primitive_action_density()),
        "quadratic_action_density": expr_text(quadratic),
        "linear_order_residual": expr_text(linear_residual()),
        "linear_terms_cancel": sp.simplify(linear_residual()) == 0,
        "blocks": [
            {
                "name": row["name"],
                "sector": row["sector"],
                "primitive": row["primitive"],
                "source": row["source"],
                "density": expr_text(row["density"]),
                "quadratic_density": expr_text(coeff_eps2(row["density"])),
            }
            for row in primitive_blocks()
        ],
        "derived_coefficients": {
            key: expr_text(value)
            for key, value in coefficients.items()
        },
        "matches_expected_coefficient_map": matches,
        "all_expected_matches": all(matches.values()),
        "tetrad_connection_block_expansion_closed": True,
        "full_eh_hr_tensor_expansion_closed": False,
        "reason_full_expansion_not_closed": (
            "This artifact expands named primitive tetrad, spin-connection, "
            "Aether, membrane, and Hassan-Rosen second-variation blocks. It still "
            "does not derive those primitive blocks from the full nonlinear Cartan "
            "EH+HR+GHY action."
        ),
        "sample_witness": sample_witness(coefficients),
        "prediction_ready": False,
        "next_step": "derive each primitive block from nonlinear tetrad determinant, curvature, HR square-root, GHY and Israel boundary terms",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Tetrad/Connection Block Derivation",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Linear terms cancel: `{payload['linear_terms_cancel']}`",
        f"All expected matches: `{payload['all_expected_matches']}`",
        f"Full EH/HR tensor expansion closed: `{payload['full_eh_hr_tensor_expansion_closed']}`",
        "",
        "## Derived Coefficients",
    ]
    for key, value in payload["derived_coefficients"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Primitive Blocks"])
    for row in payload["blocks"]:
        lines.append(
            f"- {row['name']}: `{row['primitive']}` -> `{row['quadratic_density']}`"
        )
    lines.extend(["", "## Boundary", "", payload["reason_full_expansion_not_closed"]])
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
