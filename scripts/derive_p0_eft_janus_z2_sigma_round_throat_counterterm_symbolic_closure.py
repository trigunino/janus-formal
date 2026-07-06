from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_round_throat_counterterm import (
    RoundThroatCountertermCoefficients,
    positive_round_throat_radius_roots,
    round_throat_e_counterterm_values,
    round_throat_lct_values,
)


COEFF_PATH = Path("outputs/active_z2_sigma/surface_hk_active_density_coefficients.json")
RADIUS_PATH = Path("outputs/active_z2_sigma/surface_hk_round_throat_radius_grid_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/round_throat_counterterm_symbolic_closure.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_round_throat_counterterm_symbolic_closure.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_round_throat_counterterm_symbolic_closure.json"
)


def _active(payload: dict, name: str) -> None:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{name} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{name} source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "fitted_counterterm_coefficient_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"{name} forbidden provenance flag must be false: {key}")


def _series(payload: dict, key: str, shape: tuple[int, ...]) -> np.ndarray:
    values = np.asarray(payload[key], dtype=float)
    if values.shape != shape or not np.all(np.isfinite(values)):
        raise ValueError(f"{key} must be finite and aligned")
    return values


def _optional_values(coeff_path: Path, radius_path: Path) -> dict | None:
    if not coeff_path.exists() or not radius_path.exists():
        return None
    coeff = json.loads(coeff_path.read_text(encoding="utf-8"))
    radius_payload = json.loads(radius_path.read_text(encoding="utf-8"))
    _active(coeff, "coefficients")
    _active(radius_payload, "radius")
    radius = np.asarray(radius_payload["R_Sigma_values"], dtype=float)
    shape = radius.shape
    a0 = _series(coeff, "a0_values", shape)
    a1 = _series(coeff, "a1_values", shape)
    a2 = _series(coeff, "a2_values", shape)
    a3 = _series(coeff, "a3_values", shape)
    eps = float(radius_payload.get("normal_orientation_sign", -1.0))
    lct = []
    ect = []
    for i, r_value in enumerate(radius):
        local = RoundThroatCountertermCoefficients(
            a0=float(a0[i]),
            a1=float(a1[i]),
            a2=float(a2[i]),
            a3=float(a3[i]),
            epsilon_z2=eps,
        )
        lct.append(float(round_throat_lct_values([r_value], local)[0]))
        ect.append(float(round_throat_e_counterterm_values([r_value], local)[0]))
    return {
        "a_grid": radius_payload["a_grid"],
        "R_Sigma_values": radius.tolist(),
        "L_ct_values": lct,
        "E_counterterm_values": ect,
        "positive_radius_roots_for_zero_other_terms": [
            positive_round_throat_radius_roots(
                coeff=RoundThroatCountertermCoefficients(
                    a0=float(a0[i]),
                    a1=float(a1[i]),
                    a2=float(a2[i]),
                    a3=float(a3[i]),
                    epsilon_z2=eps,
                )
            )
            for i in range(radius.size)
        ],
        "value_status": "active_coefficients_and_radius_grid_available",
    }


def build_payload(
    *,
    coeff_path: Path = COEFF_PATH,
    radius_path: Path = RADIUS_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    validation_error = None
    values = None
    try:
        values = _optional_values(coeff_path, radius_path)
    except Exception as exc:
        validation_error = str(exc)
    payload = {
        "status": "janus-z2-sigma-round-throat-counterterm-symbolic-closure",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_derivation",
        "symbolic_closure_ready": True,
        "gate_passed": True,
        "coefficient_values_available": coeff_path.exists(),
        "radius_grid_available": radius_path.exists(),
        "values_written": values is not None,
        "validation_error": validation_error,
        "round_throat_assumptions": {
            "h_ab": "diag(-1, R_Sigma^2 q_ij)",
            "K_tau_tau": "0",
            "K_ij": "epsilon_Z2 R_Sigma q_ij",
            "K_trace": "3 epsilon_Z2 / R_Sigma",
            "K_ab_Kab": "3 / R_Sigma^2",
            "sqrt_abs_h": "R_Sigma^3 sqrt(det q)",
        },
        "formulas": {
            "L_ct": "a0 + 3 epsilon_Z2 a1/R + (9 a2 + 3 a3)/R^2",
            "E_counterterm": "sqrt(det q) * (3 a0 R^2 + 6 epsilon_Z2 a1 R + 9 a2 + 3 a3)",
            "radius_equation": "E_HolstNiehYan(R) + E_matterFlux(R) + E_counterterm(R) = 0",
        },
        "values": values,
        "next_required": []
        if values is not None
        else [
            "derive_surface_hk_active_density_coefficients",
            "derive_rsigma_radius_solution_or_independent_radius_grid",
        ],
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Round Throat Counterterm Symbolic Closure",
        "",
        f"Symbolic closure ready: `{payload['symbolic_closure_ready']}`",
        f"Values written: `{payload['values_written']}`",
        "",
        "## Formula",
        f"- `L_ct = {payload['formulas']['L_ct']}`",
        f"- `E_counterterm = {payload['formulas']['E_counterterm']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
