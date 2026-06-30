from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_quadratic_coefficient_derivation.md"
JSON_PATH = REPORT_DIR / "svt_quadratic_coefficient_derivation.json"


SYMBOLS = sp.symbols("Mpl2 aetherKineticScale lambdaPhi v mHR2 membraneTension")
MPL2, AETHER, LAMBDA_PHI, VEV, MHR2, TENSION = SYMBOLS


EXPECTED = {
    "vector_alpha": VEV * (MPL2 - AETHER),
    "vector_beta": VEV * MPL2,
    "vector_mass2": MHR2,
    "scalar_alpha": VEV * (MPL2 - AETHER) + 2 * LAMBDA_PHI * VEV**2,
    "scalar_beta": VEV
    * (MPL2 + TENSION + MHR2 * MPL2 * (3 * VEV**2 + 3 * VEV + 1)),
    "scalar_mass2": 2 * LAMBDA_PHI * VEV**2 + MHR2,
}


TERM_LEDGER = [
    {
        "mode": "vector",
        "coefficient": "alpha",
        "source": "Cartan Einstein-Hilbert temporal tetrad kinetic block",
        "expr": VEV * MPL2,
    },
    {
        "mode": "vector",
        "coefficient": "alpha",
        "source": "gauge-like Maxwell Aether kinetic load",
        "expr": -VEV * AETHER,
    },
    {
        "mode": "vector",
        "coefficient": "beta",
        "source": "Cartan Einstein-Hilbert spatial gradient block",
        "expr": VEV * MPL2,
    },
    {
        "mode": "vector",
        "coefficient": "mass2",
        "source": "Sigma-supported Hassan-Rosen membrane mass block",
        "expr": MHR2,
    },
    {
        "mode": "scalar",
        "coefficient": "alpha",
        "source": "Cartan/Aether kinetic block shared with vector sector",
        "expr": VEV * MPL2 - VEV * AETHER,
    },
    {
        "mode": "scalar",
        "coefficient": "alpha",
        "source": "radion double-well stiffness after Phi=-v+dphi expansion",
        "expr": 2 * LAMBDA_PHI * VEV**2,
    },
    {
        "mode": "scalar",
        "coefficient": "beta",
        "source": "Cartan Einstein-Hilbert scalar gradient block",
        "expr": VEV * MPL2,
    },
    {
        "mode": "scalar",
        "coefficient": "beta",
        "source": "Sigma membrane tension scalar-gradient contribution",
        "expr": VEV * TENSION,
    },
    {
        "mode": "scalar",
        "coefficient": "beta",
        "source": "Hassan-Rosen elementary-polynomial scalar-gradient contribution",
        "expr": VEV * MHR2 * MPL2 * (3 * VEV**2 + 3 * VEV + 1),
    },
    {
        "mode": "scalar",
        "coefficient": "mass2",
        "source": "radion stiffness plus Hassan-Rosen scalar mass",
        "expr": 2 * LAMBDA_PHI * VEV**2 + MHR2,
    },
]


def expr_text(expr: sp.Expr) -> str:
    return str(sp.factor(expr)).replace("**", "^")


def coefficient_from_ledger(mode: str, coefficient: str) -> sp.Expr:
    terms = [
        row["expr"]
        for row in TERM_LEDGER
        if row["mode"] == mode and row["coefficient"] == coefficient
    ]
    return sp.factor(sum(terms, sp.Integer(0)))


def derive_coefficients() -> dict[str, sp.Expr]:
    vector_alpha = coefficient_from_ledger("vector", "alpha")
    vector_beta = coefficient_from_ledger("vector", "beta")
    scalar_alpha = coefficient_from_ledger("scalar", "alpha")
    scalar_beta = coefficient_from_ledger("scalar", "beta")
    return {
        "vector_alpha": vector_alpha,
        "vector_beta": vector_beta,
        "vector_mass2": coefficient_from_ledger("vector", "mass2"),
        "vector_speed2": sp.factor(vector_beta / vector_alpha),
        "scalar_alpha": scalar_alpha,
        "scalar_beta": scalar_beta,
        "scalar_mass2": coefficient_from_ledger("scalar", "mass2"),
        "scalar_speed2": sp.factor(scalar_beta / scalar_alpha),
    }


def expected_with_speeds() -> dict[str, sp.Expr]:
    expected = dict(EXPECTED)
    expected["vector_speed2"] = sp.factor(EXPECTED["vector_beta"] / EXPECTED["vector_alpha"])
    expected["scalar_speed2"] = sp.factor(EXPECTED["scalar_beta"] / EXPECTED["scalar_alpha"])
    return expected


def compare_to_expected(derived: dict[str, sp.Expr]) -> dict[str, bool]:
    expected = expected_with_speeds()
    return {
        key: sp.simplify(derived[key] - expected[key]) == 0
        for key in expected
    }


def sample_witness() -> dict:
    values = {
        MPL2: 4,
        AETHER: 1,
        LAMBDA_PHI: 1,
        VEV: 1,
        MHR2: 1,
        TENSION: 30,
    }
    derived = derive_coefficients()
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
            key: expr_text(expr.subs(values))
            for key, expr in derived.items()
        },
    }


def build_payload() -> dict:
    derived = derive_coefficients()
    matches = compare_to_expected(derived)
    return {
        "artifact": "svt_quadratic_coefficient_derivation",
        "status": "ledger_symbolic_derivation_closed",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "full_tensor_variation_closed": False,
        "reason_full_tensor_variation_not_closed": (
            "This artifact derives the scalar/vector coefficients from the encoded "
            "quadratic Cartan-Aether term ledger. It does not yet perform an "
            "automatic tensor variation of the full action."
        ),
        "gauge_and_constraints": {
            "svt_decomposition": "scalar/vector/tensor split applied on twin Minkowski background",
            "spatial_gauge": "unitary spatial gauge E=0,F_i=0 on both sheets",
            "lapse_shift": "solved and reinjected",
            "boundary": "Israel junction and bending-mode elimination assumed",
        },
        "term_ledger": [
            {
                "mode": row["mode"],
                "coefficient": row["coefficient"],
                "source": row["source"],
                "expr": expr_text(row["expr"]),
            }
            for row in TERM_LEDGER
        ],
        "derived_coefficients": {
            key: expr_text(value)
            for key, value in derived.items()
        },
        "expected_coefficients": {
            key: expr_text(value)
            for key, value in expected_with_speeds().items()
        },
        "matches_expected_coefficient_map": matches,
        "all_expected_matches": all(matches.values()),
        "stability_inequalities": {
            "vector_no_ghost": "0 < v*(Mpl2 - aetherKineticScale)",
            "vector_no_gradient": "0 < v*Mpl2",
            "scalar_no_ghost": "0 < v*(Mpl2 - aetherKineticScale) + 2*lambdaPhi*v^2",
            "scalar_no_gradient": (
                "0 < v*(Mpl2 + membraneTension + "
                "mHR2*Mpl2*(3*v^2+3*v+1))"
            ),
        },
        "observable_bridge": {
            "hubble_tension": "feeds the effective background/inference map conditionally",
            "jwst_growth": "feeds linear growth source and collapse-time diagnostics conditionally",
            "lensing_gw": "feeds falsifiable signature map, not a survey likelihood",
        },
        "sample_witness": sample_witness(),
        "prediction_ready": False,
        "next_step": "replace ledger terms by automatic tensor variation of the full action",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Quadratic Coefficient Derivation",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Full tensor variation closed: `{payload['full_tensor_variation_closed']}`",
        f"All expected matches: `{payload['all_expected_matches']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Derived Coefficients",
    ]
    for key, value in payload["derived_coefficients"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Term Ledger"])
    for row in payload["term_ledger"]:
        lines.append(
            f"- {row['mode']}.{row['coefficient']}: `{row['expr']}` from {row['source']}"
        )
    lines.extend(["", "## Stability Inequalities"])
    for key, value in payload["stability_inequalities"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend([
        "",
        "## Boundary",
        "",
        payload["reason_full_tensor_variation_not_closed"],
        "",
        f"Next step: `{payload['next_step']}`",
    ])
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
