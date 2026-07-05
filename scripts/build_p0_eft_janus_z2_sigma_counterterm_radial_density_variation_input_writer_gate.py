from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


GEOMETRY_PATH = Path("outputs/active_z2_sigma/counterterm_radial_geometry_factors.json")
PROFILE_PATH = Path("outputs/active_z2_sigma/counterterm_lct_radial_profile.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_radial_density_variation_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_radial_density_variation_input_writer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_radial_density_variation_input_writer_gate.json"
)


def _reject_forbidden(payload: dict) -> None:
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
            raise ValueError(f"Forbidden provenance flag must be false: {key}")


def _load_geometry(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("geometry active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("geometry source must be active_derived")
    _reject_forbidden(payload)
    if payload.get("geometry_factors_ready") is not True:
        raise ValueError("geometry_factors_ready must be true")
    dim = int(payload["dimension"])
    sqrt_det_q = float(payload["sqrt_det_unit_q"])
    if dim <= 0 or not np.isfinite(sqrt_det_q) or sqrt_det_q <= 0.0:
        raise ValueError("geometry dimension and sqrt_det_unit_q must be positive")
    return {"dimension": dim, "sqrt_det_unit_q": sqrt_det_q}


def _load_profile(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("L_ct profile active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("L_ct profile source must be active_derived")
    _reject_forbidden(payload)
    if payload.get("L_ct_profile_ready") is not True:
        raise ValueError("L_ct_profile_ready must be true")
    for key in ["a_grid", "R_Sigma_values", "L_ct_values", "partial_R_L_ct_values"]:
        if key not in payload:
            raise ValueError(f"L_ct profile missing {key}")
    return payload


def _aligned_array(payload: dict, key: str, shape: tuple[int, ...]) -> np.ndarray:
    values = np.asarray(payload[key], dtype=float)
    if values.shape != shape or not np.all(np.isfinite(values)):
        raise ValueError(f"{key} must be finite and aligned with a_grid")
    return values


def _build_output(geometry: dict, profile: dict) -> dict:
    a_grid = np.asarray(profile["a_grid"], dtype=float)
    if a_grid.ndim != 1 or len(a_grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(a_grid <= 0.0) or np.any(np.diff(a_grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    shape = a_grid.shape
    R = _aligned_array(profile, "R_Sigma_values", shape)
    L_ct = _aligned_array(profile, "L_ct_values", shape)
    partial_R_L_ct = _aligned_array(profile, "partial_R_L_ct_values", shape)
    if np.any(R <= 0.0):
        raise ValueError("R_Sigma_values must be positive")
    dim = geometry["dimension"]
    sqrt_det_q = geometry["sqrt_det_unit_q"]
    sqrt_abs_h = (R ** dim) * sqrt_det_q
    partial_R_sqrt_abs_h = dim * (R ** (dim - 1)) * sqrt_det_q
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "counterterm_density_explicit": True,
        "radial_variation_ready": True,
        "a_grid": a_grid.tolist(),
        "R_Sigma_values": R.tolist(),
        "sqrt_abs_h_values": sqrt_abs_h.tolist(),
        "partial_R_sqrt_abs_h_values": partial_R_sqrt_abs_h.tolist(),
        "L_ct_values": L_ct.tolist(),
        "partial_R_L_ct_values": partial_R_L_ct.tolist(),
        "density_variation_formula": "partial_R(sqrt_abs_h * L_ct)",
        "geometry_source": "counterterm_radial_geometry_factors",
        "profile_source": "counterterm_lct_radial_profile",
    }


def build_payload(
    *,
    geometry_path: Path = GEOMETRY_PATH,
    profile_path: Path = PROFILE_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = {
        "counterterm_radial_geometry_factors": geometry_path.exists(),
        "counterterm_lct_radial_profile": profile_path.exists(),
    }
    output_written = False
    validation_error = None
    if all(input_exists.values()):
        try:
            output = _build_output(_load_geometry(geometry_path), _load_profile(profile_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-counterterm-radial-density-variation-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "output_manifest": str(output_path),
        "counterterm_radial_density_variation_inputs_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "counterterm_lct_radial_profile",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_counterterm_residual_scalar_contractions_inputs",
            "run_counterterm_lct_radial_profile_from_residual_contractions",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Radial Density Variation Input Writer Gate",
        "",
        f"Output written: `{payload['counterterm_radial_density_variation_inputs_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
