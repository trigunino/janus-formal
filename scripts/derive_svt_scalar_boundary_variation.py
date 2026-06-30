from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import MHR2, MPL2, VEV, expr_text
    from scripts.derive_svt_scalar_boundary_constraint_gate import (
        boundary_constraint_residual,
        constrained_single_mode_alpha,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import MHR2, MPL2, VEV, expr_text
    from derive_svt_scalar_boundary_constraint_gate import (
        boundary_constraint_residual,
        constrained_single_mode_alpha,
    )


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_scalar_boundary_variation.md"
JSON_PATH = REPORT_DIR / "svt_scalar_boundary_variation.json"

K = sp.Symbol("k", nonzero=True)
ZETA, PSI_P, CHI = sp.symbols("zeta psi_p chi")


def h_psi_psi() -> sp.Expr:
    return sp.factor(3 * (1 + 1 / VEV))


def hr_psi_surface_term() -> sp.Expr:
    return sp.factor(
        -MHR2 * MPL2 * h_psi_psi() * (1 + 1 / VEV) ** 2 * PSI_P**2
    )


def cartan_ghy_surface_term() -> sp.Expr:
    return sp.factor(K**2 * ZETA * (CHI / sp.sqrt(VEV) - 2 * MPL2 * PSI_P))


def surface_density() -> sp.Expr:
    return sp.factor(cartan_ghy_surface_term() + hr_psi_surface_term())


def zeta_variation() -> sp.Expr:
    return sp.factor(sp.diff(surface_density(), ZETA))


def constraint_from_variation() -> sp.Expr:
    return sp.factor(CHI - sp.solve(zeta_variation(), CHI)[0])


def psi_variation() -> sp.Expr:
    return sp.factor(sp.diff(surface_density(), PSI_P))


def build_payload() -> dict:
    sample = {MPL2: 4, VEV: 1}
    alpha = constrained_single_mode_alpha()
    return {
        "artifact": "svt_scalar_boundary_variation",
        "status": "boundary_constraint_derived_from_supplied_surface_density",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "surface_density": expr_text(surface_density()),
        "terms": {
            "cartan_ghy": expr_text(cartan_ghy_surface_term()),
            "hr_psi": expr_text(hr_psi_surface_term()),
        },
        "variations": {
            "dL_dzeta": expr_text(zeta_variation()),
            "d_hr_dzeta": expr_text(sp.diff(hr_psi_surface_term(), ZETA)),
            "dL_dpsi_p": expr_text(psi_variation()),
        },
        "constraint": {
            "from_zeta_variation": expr_text(constraint_from_variation()),
            "matches_gate_residual": sp.simplify(
                constraint_from_variation() - boundary_constraint_residual().subs(
                    {
                        sp.Symbol("psi_p"): PSI_P,
                        sp.Symbol("chi"): CHI,
                    }
                )
            )
            == 0,
        },
        "reduced_scalar_mode": {
            "alpha": expr_text(alpha),
            "sample_Mpl2_4_v_1_alpha": expr_text(alpha.subs(sample)),
            "sample_positive": bool(alpha.subs(sample) > 0),
        },
        "gate": {
            "variation_from_supplied_surface_density_closed": True,
            "surface_density_derived_from_full_cartan_ghy": False,
            "conditional_no_ghost_closed": True,
            "prediction_ready": False,
        },
        "needed_inputs": [
            "derive this surface density from the full Cartan GHY boundary action",
            "verify the missing-or-present Mpl2 factor in the chi*zeta term from dimensions",
            "derive the HR/tension background balance instead of using only the psi variation record",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Scalar Boundary Variation",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['gate']['prediction_ready']}`",
        "",
        "## Variation",
        f"- dL_dzeta: `{payload['variations']['dL_dzeta']}`",
        f"- constraint: `{payload['constraint']['from_zeta_variation']}`",
        f"- sample alpha: `{payload['reduced_scalar_mode']['sample_Mpl2_4_v_1_alpha']}`",
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
