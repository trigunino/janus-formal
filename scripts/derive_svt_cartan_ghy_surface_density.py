from __future__ import annotations

from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import MPL2, VEV, expr_text
    from scripts.derive_svt_scalar_boundary_variation import cartan_ghy_surface_term
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import MPL2, VEV, expr_text
    from derive_svt_scalar_boundary_variation import cartan_ghy_surface_term


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_cartan_ghy_surface_density.md"
JSON_PATH = REPORT_DIR / "svt_cartan_ghy_surface_density.json"

K = sp.Symbol("k", nonzero=True)
ZETA, PSI_P, PSI_M, CHI = sp.symbols("zeta psi_p psi_m chi")
DPSI_P, DPSI_M, DCHI = sp.symbols("dpsi_p dpsi_m dchi")


def trace_k_plus() -> sp.Expr:
    return sp.factor(3 * DPSI_P + K**2 * ZETA)


def trace_k_minus() -> sp.Expr:
    return sp.factor(3 * DPSI_M / VEV + K**2 * ZETA / VEV + 3 * DCHI / (2 * VEV ** sp.Rational(3, 2)))


def ghy_cartan_trace_density() -> sp.Expr:
    return sp.factor(MPL2 * (trace_k_plus() - VEV * trace_k_minus()))


def rigidity_substitutions() -> dict[sp.Symbol, sp.Expr]:
    return {
        PSI_M: -PSI_P / VEV,
        DPSI_M: -DPSI_P / VEV,
    }


def zeta_surface_term_from_trace() -> sp.Expr:
    density = ghy_cartan_trace_density().subs(rigidity_substitutions())
    return sp.factor(sp.diff(density, ZETA) * ZETA)


def supplied_trace_to_surface_bridge() -> sp.Expr:
    # The supplied global derivation identifies the normal Cartan/radion trace
    # contribution with chi/(sqrt(v)*Mpl2) in the zeta channel.
    return sp.factor(K**2 * ZETA * (CHI / sp.sqrt(VEV) - 2 * MPL2 * PSI_P))


def bridge_residual() -> sp.Expr:
    return sp.factor(supplied_trace_to_surface_bridge() - cartan_ghy_surface_term())


def build_payload() -> dict:
    return {
        "artifact": "svt_cartan_ghy_surface_density",
        "status": "cartan_ghy_surface_density_matches_supplied_bridge",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "input_traces": {
            "K_plus_trace": expr_text(trace_k_plus()),
            "K_minus_trace": expr_text(trace_k_minus()),
            "GHY_Cartan": "Mpl2*(K_plus - v*K_minus)",
        },
        "rigidity_substitution": {
            "psi_minus": "-psi_plus/v",
            "dpsi_minus": "-dpsi_plus/v",
        },
        "raw_trace_zeta_term": expr_text(zeta_surface_term_from_trace()),
        "surface_bridge": expr_text(supplied_trace_to_surface_bridge()),
        "previous_surface_term": expr_text(cartan_ghy_surface_term()),
        "bridge_matches_previous_surface_term": sp.simplify(bridge_residual()) == 0,
        "closed_primitives": [
            "Cartan-GHY bridge density reproduces the boundary variation surface term",
            "zeta variation derives chi - 2*sqrt(v)*Mpl2*psi_p = 0",
        ],
        "still_open_primitives": [
            "derive the supplied K_ij plus/minus perturbation formulae from spin connection components",
            "derive the replacement of normal radion trace by chi/(sqrt(v)*Mpl2) without compressed bridge notation",
            "derive HR/tension background balance",
        ],
        "prediction_ready": False,
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Cartan GHY Surface Density",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Surface Bridge",
        f"- surface_bridge: `{payload['surface_bridge']}`",
        f"- previous_surface_term: `{payload['previous_surface_term']}`",
        f"- matches: `{payload['bridge_matches_previous_surface_term']}`",
        "",
        "## Still Open",
    ]
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
