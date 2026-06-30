from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import MPL2, VEV, expr_text
    from scripts.derive_svt_scalar_canonical_basis_check import constrained_single_mode_alpha
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import MPL2, VEV, expr_text
    from derive_svt_scalar_canonical_basis_check import constrained_single_mode_alpha


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_scalar_boundary_constraint_gate.md"
JSON_PATH = REPORT_DIR / "svt_scalar_boundary_constraint_gate.json"

PSI_P, CHI = sp.symbols("psi_p chi")


def boundary_constraint_residual() -> sp.Expr:
    return sp.factor(CHI - 2 * sp.sqrt(VEV) * MPL2 * PSI_P)


def sample_alpha() -> sp.Expr:
    return sp.factor(constrained_single_mode_alpha().subs({MPL2: 4, VEV: 1}))


def build_payload() -> dict:
    alpha = constrained_single_mode_alpha()
    return {
        "artifact": "svt_scalar_boundary_constraint_gate",
        "status": "boundary_constraint_closes_scalar_ghost_conditionally",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "constraint": {
            "residual": expr_text(boundary_constraint_residual()),
            "claimed_origin": "trace Israel/Cartan boundary equation on Sigma",
            "implemented_as_derived_from_action": False,
        },
        "reduced_scalar_mode": {
            "alpha": expr_text(alpha),
            "sample_Mpl2_4_v_1_alpha": expr_text(sample_alpha()),
            "sample_positive": bool(sample_alpha() > 0),
        },
        "gate": {
            "conditional_no_ghost_closed": True,
            "unconditional_no_ghost_closed": False,
            "prediction_ready": False,
            "reason": (
                "The constraint gives a positive single scalar mode, but the "
                "boundary variation deriving it is not yet implemented."
            ),
        },
        "needed_inputs": [
            "explicit boundary action term whose variation gives chi - 2*sqrt(v)*Mpl2*psi_p = 0",
            "normal Cartan connection contribution to the traced Israel equation",
            "sign and normalization of the HR boundary stress in that traced equation",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Scalar Boundary Constraint Gate",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['gate']['prediction_ready']}`",
        "",
        "## Constraint",
        f"- residual: `{payload['constraint']['residual']}`",
        f"- implemented_as_derived_from_action: `{payload['constraint']['implemented_as_derived_from_action']}`",
        "",
        "## Reduced Mode",
        f"- alpha: `{payload['reduced_scalar_mode']['alpha']}`",
        f"- sample_Mpl2_4_v_1_alpha: `{payload['reduced_scalar_mode']['sample_Mpl2_4_v_1_alpha']}`",
        "",
        "## Needed Inputs",
    ]
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
