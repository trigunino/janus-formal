from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_background_branch_classifier import background_balance_residual
    from scripts.derive_svt_quadratic_coefficients import MPL2, MHR2, TENSION, VEV, expr_text
    from scripts.derive_svt_scalar_exact_hr_source_reduction import (
        PHI_M,
        PHI_P,
        PSI_P,
        exact_hr_sources,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_background_branch_classifier import background_balance_residual
    from derive_svt_quadratic_coefficients import MPL2, MHR2, TENSION, VEV, expr_text
    from derive_svt_scalar_exact_hr_source_reduction import (
        PHI_M,
        PHI_P,
        PSI_P,
        exact_hr_sources,
    )


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_curved_branch_desitter_seed.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_desitter_seed.json"

K, A, H, DPSI_P = sp.symbols("k a H dpsi_p", nonzero=True)


def h2_from_background_residual() -> sp.Expr:
    return sp.factor(-background_balance_residual() / (12 * MPL2))


def k_phys2() -> sp.Expr:
    return sp.factor(K**2 / A**2)


def flrw_measure() -> sp.Expr:
    return A**3


def eh_plus_desitter_density() -> sp.Expr:
    return sp.factor(
        MPL2
        * flrw_measure()
        * (
            -3 * DPSI_P**2
            + 9 * H**2 * PSI_P**2
            + 2 * k_phys2() * PHI_P * PSI_P
            - k_phys2() * PSI_P**2
            - 6 * H * PHI_P * DPSI_P
        )
    )


def lapse_plus_desitter_constraint() -> sp.Expr:
    return sp.factor(
        MPL2 * (2 * k_phys2() * PSI_P - 6 * H * DPSI_P)
        - exact_hr_sources()["dS_d_phi_p"]
    )


def solve_phi_difference_from_lapse_plus() -> sp.Expr:
    phi_p_solution = sp.solve(lapse_plus_desitter_constraint(), PHI_P, dict=True)[0][PHI_P]
    return sp.factor(phi_p_solution - PHI_M)


def build_payload() -> dict:
    t30 = {VEV: 1, MHR2: 1, MPL2: 4, TENSION: 30}
    t6 = {VEV: 1, MHR2: 1, MPL2: 4, TENSION: 6}
    h2 = h2_from_background_residual()
    return {
        "artifact": "svt_curved_branch_desitter_seed",
        "status": "curved_branch_desitter_seed_encoded_not_full_svt_closed",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "background": {
            "residual_to_H2": "3*Mpl2*H^2 = -Delta/4",
            "H2": expr_text(h2),
            "T30_v1_m1_Mpl4_H2": expr_text(h2.subs(t30)),
            "T6_v1_m1_Mpl4_H2": expr_text(h2.subs(t6)),
            "scale_factor": "a(t)=exp(H*t)",
        },
        "replacements": {
            "measure": expr_text(flrw_measure()),
            "k_phys2": expr_text(k_phys2()),
        },
        "eh_plus_desitter_density": expr_text(eh_plus_desitter_density()),
        "lapse_plus_desitter_constraint": expr_text(lapse_plus_desitter_constraint()),
        "phi_p_minus_phi_m_from_lapse_plus": expr_text(solve_phi_difference_from_lapse_plus()),
        "closed_primitives": [
            "residual background tension mapped to H^2",
            "plus-sector dS lapse constraint encoded with H friction",
            "HR phi source reused in curved branch seed",
        ],
        "still_open_primitives": [
            "minus-sector dS EH quadratic action with asymmetric lapse v",
            "curved shift constraints and bending equation",
            "full curved-branch reinjection and kinetic/gradient matrix",
            "sign convention mapping residual to dS versus AdS must be sourced",
        ],
        "prediction_ready": False,
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch de Sitter Seed",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Background",
    ]
    for key, value in payload["background"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Lapse Plus",
            f"- constraint: `{payload['lapse_plus_desitter_constraint']}`",
            f"- phi_p_minus_phi_m: `{payload['phi_p_minus_phi_m_from_lapse_plus']}`",
            "",
            "## Still Open",
        ]
    )
    lines.extend(f"- {item}" for item in payload["still_open_primitives"])
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
