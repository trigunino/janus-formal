from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_surface_hk import polynomial_surface_hk_isotropic_alpha_components


GEOMETRY_PATH = Path("outputs/active_z2_sigma/surface_hk_radial_geometry_inputs.json")
COEFFICIENT_PATH = Path("outputs/active_z2_sigma/surface_hk_active_density_coefficients.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/surface_hk_alpha_radial_projection_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_projection_input_writer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_projection_input_writer_gate.json"
)


def _load_active(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "fitted_counterterm_coefficient_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    return payload


def _array(payload: dict, key: str, shape: tuple[int, ...]) -> np.ndarray:
    values = np.asarray(payload[key], dtype=float)
    if values.shape != shape:
        raise ValueError(f"{key} has shape {values.shape}, expected {shape}")
    if not np.all(np.isfinite(values)):
        raise ValueError(f"{key} contains non-finite values")
    return values


def build_payload(
    *,
    geometry_path: Path = GEOMETRY_PATH,
    coefficient_path: Path = COEFFICIENT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    geometry_exists = geometry_path.exists()
    coefficient_exists = coefficient_path.exists()
    output_written = False
    validation_error = None
    if geometry_exists and coefficient_exists:
        try:
            geometry = _load_active(geometry_path)
            coeff = _load_active(coefficient_path)
            grid = np.asarray(geometry["a_grid"], dtype=float)
            if grid.ndim != 1 or len(grid) < 1:
                raise ValueError("a_grid must be one-dimensional")
            shape = grid.shape
            if coeff["a_grid"] != geometry["a_grid"]:
                raise ValueError("coefficient and geometry a_grid must match exactly")
            components = polynomial_surface_hk_isotropic_alpha_components(
                a0=_array(coeff, "a0_values", shape),
                a1=_array(coeff, "a1_values", shape),
                a2=_array(coeff, "a2_values", shape),
                a3=_array(coeff, "a3_values", shape),
                K_tau=_array(geometry, "K_tau_values", shape),
                K_s=_array(geometry, "K_s_values", shape),
            )
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "observational_H0_fit_used": False,
                "observational_curvature_fit_used": False,
                "fitted_counterterm_coefficient_used": False,
                "a_grid": geometry["a_grid"],
                "R_Sigma_values": geometry["R_Sigma_values"],
                "sqrt_abs_h_values": geometry["sqrt_abs_h_values"],
                "alpha_h_tau_values": components["alpha_h_tau"].tolist(),
                "alpha_h_s_values": components["alpha_h_s"].tolist(),
                "alpha_K_tau_values": components["alpha_K_tau"].tolist(),
                "alpha_K_s_values": components["alpha_K_s"].tolist(),
                "partial_R_h_tau_values": geometry["partial_R_h_tau_values"],
                "partial_R_h_s_values": geometry["partial_R_h_s_values"],
                "partial_R_K_tau_values": geometry["partial_R_K_tau_values"],
                "partial_R_K_s_values": geometry["partial_R_K_s_values"],
                "K_trace_values": components["K_trace"].tolist(),
                "L_Sigma_values": components["L_Sigma"].tolist(),
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-surface-hk-projection-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "geometry_manifest": str(geometry_path),
        "coefficient_manifest": str(coefficient_path),
        "output_manifest": str(output_path),
        "geometry_exists": geometry_exists,
        "coefficient_exists": coefficient_exists,
        "surface_hk_projection_inputs_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none"
        if output_written
        else "surface_hk_radial_geometry_inputs_and_active_density_coefficients",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_surface_hk_radial_geometry_inputs",
            "derive_surface_hk_active_density_coefficients",
            "then_run_surface_hk_alpha_radial_projection_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Surface h/K Projection Input Writer Gate",
        "",
        f"Geometry exists: `{payload['geometry_exists']}`",
        f"Coefficients exist: `{payload['coefficient_exists']}`",
        f"Output written: `{payload['surface_hk_projection_inputs_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
