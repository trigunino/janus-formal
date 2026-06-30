from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import (
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
REPORT_PATH = REPORT_DIR / "svt_hr_membrane_primitive_derivation.md"
JSON_PATH = REPORT_DIR / "svt_hr_membrane_primitive_derivation.json"

BETA1, BETA2, BETA3 = sp.symbols("beta1 beta2 beta3")


def stable_hr_beta_line() -> dict[sp.Symbol, sp.Integer]:
    return {
        BETA1: sp.Integer(1),
        BETA2: sp.Integer(3),
        BETA3: sp.Integer(3),
    }


def hr_square_root_scalar_weight() -> sp.Expr:
    polynomial = BETA1 + BETA2 * VEV + BETA3 * VEV**2
    return sp.factor(polynomial.subs(stable_hr_beta_line()))


def membrane_gradient_density() -> sp.Expr:
    return -sp.Rational(1, 2) * TENSION * background_measure() * (EPS * GRAD_S) ** 2


def hr_square_root_gradient_density() -> sp.Expr:
    return (
        -sp.Rational(1, 2)
        * MHR2
        * MPL2
        * background_measure()
        * hr_square_root_scalar_weight()
        * (EPS * GRAD_S) ** 2
    )


def primitive_eps2_blocks() -> dict[str, sp.Expr]:
    return {
        "scalar_membrane_gradient_density": coeff_eps2(membrane_gradient_density()),
        "scalar_hr_square_root_gradient_density": coeff_eps2(
            hr_square_root_gradient_density()
        ),
    }


def derived_coefficients() -> dict[str, sp.Expr]:
    blocks = primitive_eps2_blocks()
    membrane = -sp.diff(blocks["scalar_membrane_gradient_density"], GRAD_S, 2)
    hr = -sp.diff(blocks["scalar_hr_square_root_gradient_density"], GRAD_S, 2)
    return {
        "scalar_beta_membrane": sp.factor(membrane),
        "scalar_beta_hr": sp.factor(hr),
        "scalar_beta_membrane_plus_hr": sp.factor(membrane + hr),
    }


def expected_coefficients() -> dict[str, sp.Expr]:
    membrane = VEV * TENSION
    hr = VEV * MHR2 * MPL2 * (3 * VEV**2 + 3 * VEV + 1)
    return {
        "scalar_beta_membrane": membrane,
        "scalar_beta_hr": hr,
        "scalar_beta_membrane_plus_hr": membrane + hr,
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
        "artifact": "svt_hr_membrane_primitive_derivation",
        "status": "hr_square_root_and_membrane_gradient_primitives_closed",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "hr_beta_line": {
            "beta1": 1,
            "beta2": 3,
            "beta3": 3,
            "beta4": 1,
            "note": "beta4 is not used by this scalar-gradient weight",
        },
        "hr_square_root_scalar_weight": expr_text(hr_square_root_scalar_weight()),
        "background_measure": expr_text(background_measure()),
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
            "Hassan-Rosen stable beta-line scalar-gradient weight",
            "Sigma membrane gradient normalization by induced background measure",
        ],
        "still_open_primitives": [
            "full HR square-root matrix variation, beyond the diagonal scalar-gradient branch",
            "GHY/Israel derivation of the membrane normalization, beyond the encoded induced-measure branch",
            "radion potential mass term separated from kinetic stiffness",
        ],
        "prediction_ready": False,
        "next_step": "derive HR square-root matrix variation and GHY/Israel normalization without diagonal-branch reduction",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT HR/Membrane Primitive Derivation",
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
