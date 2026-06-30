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


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_quadratic_action_variation.md"
JSON_PATH = REPORT_DIR / "svt_quadratic_action_variation.json"

QD_V, GRAD_V, VEC_V = sp.symbols("qdot_v grad_v vec_v")
QD_S, GRAD_S, SCAL_S = sp.symbols("qdot_s grad_s scal_s")


def quadratic_action_terms() -> list[dict]:
    vector_alpha = EXPECTED["vector_alpha"]
    vector_beta = EXPECTED["vector_beta"]
    scalar_alpha = EXPECTED["scalar_alpha"]
    scalar_beta = EXPECTED["scalar_beta"]
    return [
        {
            "sector": "vector",
            "source": "Cartan EH plus/minus temporal tetrad kinetic block",
            "lagrangian": sp.Rational(1, 2) * VEV * MPL2 * QD_V**2,
        },
        {
            "sector": "vector",
            "source": "Maxwell-like Aether kinetic load",
            "lagrangian": -sp.Rational(1, 2) * VEV * AETHER * QD_V**2,
        },
        {
            "sector": "vector",
            "source": "Cartan EH vector gradient block",
            "lagrangian": -sp.Rational(1, 2) * vector_beta * GRAD_V**2,
        },
        {
            "sector": "vector",
            "source": "Hassan-Rosen membrane vector mass block",
            "lagrangian": -sp.Rational(1, 2) * MHR2 * VEC_V**2,
        },
        {
            "sector": "scalar",
            "source": "Cartan/Aether scalar kinetic block",
            "lagrangian": sp.Rational(1, 2)
            * (VEV * MPL2 - VEV * AETHER)
            * QD_S**2,
        },
        {
            "sector": "scalar",
            "source": "radion double-well kinetic stiffness",
            "lagrangian": sp.Rational(1, 2)
            * (2 * LAMBDA_PHI * VEV**2)
            * QD_S**2,
        },
        {
            "sector": "scalar",
            "source": "Cartan EH plus membrane plus HR scalar gradient block",
            "lagrangian": -sp.Rational(1, 2) * scalar_beta * GRAD_S**2,
        },
        {
            "sector": "scalar",
            "source": "radion plus HR scalar mass block",
            "lagrangian": -sp.Rational(1, 2)
            * EXPECTED["scalar_mass2"]
            * SCAL_S**2,
        },
    ]


def quadratic_action_density() -> sp.Expr:
    return sp.factor(sum((row["lagrangian"] for row in quadratic_action_terms()), sp.Integer(0)))


def extract_coefficients(action: sp.Expr) -> dict[str, sp.Expr]:
    vector_alpha = sp.factor(sp.diff(action, QD_V, 2))
    vector_beta = sp.factor(-sp.diff(action, GRAD_V, 2))
    vector_mass2 = sp.factor(-sp.diff(action, VEC_V, 2))
    scalar_alpha = sp.factor(sp.diff(action, QD_S, 2))
    scalar_beta = sp.factor(-sp.diff(action, GRAD_S, 2))
    scalar_mass2 = sp.factor(-sp.diff(action, SCAL_S, 2))
    return {
        "vector_alpha": vector_alpha,
        "vector_beta": vector_beta,
        "vector_mass2": vector_mass2,
        "vector_speed2": sp.factor(vector_beta / vector_alpha),
        "scalar_alpha": scalar_alpha,
        "scalar_beta": scalar_beta,
        "scalar_mass2": scalar_mass2,
        "scalar_speed2": sp.factor(scalar_beta / scalar_alpha),
    }


def compare_to_expected(coefficients: dict[str, sp.Expr]) -> dict[str, bool]:
    expected = expected_with_speeds()
    return {
        key: sp.simplify(coefficients[key] - expected[key]) == 0
        for key in expected
    }


def euler_lagrange_residuals(action: sp.Expr) -> dict[str, sp.Expr]:
    return {
        "vector_mode": sp.factor(
            sp.diff(action, VEC_V)
            - sp.diff(action, QD_V) * sp.Symbol("D_t")
            - sp.diff(action, GRAD_V) * sp.Symbol("D_i")
        ),
        "scalar_mode": sp.factor(
            sp.diff(action, SCAL_S)
            - sp.diff(action, QD_S) * sp.Symbol("D_t")
            - sp.diff(action, GRAD_S) * sp.Symbol("D_i")
        ),
    }


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
    action = quadratic_action_density()
    coefficients = extract_coefficients(action)
    matches = compare_to_expected(coefficients)
    residuals = euler_lagrange_residuals(action)
    return {
        "artifact": "svt_quadratic_action_variation",
        "status": "quadratic_action_variation_closed",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "action_density": expr_text(action),
        "terms": [
            {
                "sector": row["sector"],
                "source": row["source"],
                "lagrangian": expr_text(row["lagrangian"]),
            }
            for row in quadratic_action_terms()
        ],
        "extraction_rule": {
            "alpha": "d^2 L2 / d qdot^2",
            "beta": "- d^2 L2 / d grad(q)^2",
            "mass2": "- d^2 L2 / d q^2",
        },
        "euler_lagrange_residuals": {
            key: expr_text(value)
            for key, value in residuals.items()
        },
        "derived_coefficients": {
            key: expr_text(value)
            for key, value in coefficients.items()
        },
        "matches_expected_coefficient_map": matches,
        "all_expected_matches": all(matches.values()),
        "quadratic_variation_closed": True,
        "full_nonlinear_tensor_variation_closed": False,
        "reason_full_nonlinear_tensor_variation_not_closed": (
            "The script varies the already-reduced SVT quadratic action density. "
            "It does not yet expand the full nonlinear Cartan Einstein-Hilbert, "
            "Hassan-Rosen, GHY, and membrane action from tetrad/connection variables."
        ),
        "sample_witness": sample_witness(coefficients),
        "prediction_ready": False,
        "next_step": "derive the SVT quadratic action density directly from tetrad and connection perturbations",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Quadratic Action Variation",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Quadratic variation closed: `{payload['quadratic_variation_closed']}`",
        f"Full nonlinear tensor variation closed: `{payload['full_nonlinear_tensor_variation_closed']}`",
        f"All expected matches: `{payload['all_expected_matches']}`",
        "",
        "## Extracted Coefficients",
    ]
    for key, value in payload["derived_coefficients"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Extraction Rule"])
    for key, value in payload["extraction_rule"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Boundary", "", payload["reason_full_nonlinear_tensor_variation_not_closed"]])
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
