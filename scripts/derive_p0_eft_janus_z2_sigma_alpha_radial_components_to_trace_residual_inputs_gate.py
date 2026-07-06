from __future__ import annotations

import json
from pathlib import Path

import numpy as np


INPUT_PATH = Path("outputs/active_z2_sigma/counterterm_alpha_res_radial_components.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_trace_residual_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_alpha_radial_components_to_trace_residual_inputs_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_alpha_radial_components_to_trace_residual_inputs_gate.json"
)


def _active(payload: dict) -> None:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("input source must be active_derived")
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
            raise ValueError(f"forbidden provenance flag must be false: {key}")


def _array(payload: dict, key: str, shape: tuple[int, ...]) -> np.ndarray:
    values = np.asarray(payload[key], dtype=float)
    if values.shape != shape or not np.all(np.isfinite(values)):
        raise ValueError(f"{key} must be finite and aligned")
    return values


def _build_trace_inputs(source: dict) -> dict:
    _active(source)
    grid = np.asarray(source["a_grid"], dtype=float)
    if grid.ndim != 1 or grid.size < 1:
        raise ValueError("a_grid must be one-dimensional")
    radius = _array(source, "R_Sigma_values", grid.shape)
    sqrt_abs_h = _array(source, "sqrt_abs_h_values", grid.shape)
    alpha_h_radial = _array(source, "alpha_h_radial_coefficient_values", grid.shape)
    alpha_k_radial = _array(source, "alpha_K_radial_coefficient_values", grid.shape)
    if np.any(radius <= 0.0) or np.any(sqrt_abs_h <= 0.0):
        raise ValueError("R_Sigma_values and sqrt_abs_h_values must be positive")
    r_h_trace = alpha_h_radial / (2.0 * radius * sqrt_abs_h)
    r_k_trace = alpha_k_radial / sqrt_abs_h
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
        "a_grid": grid.tolist(),
        "R_h_trace_values": r_h_trace.tolist(),
        "R_K_trace_values": r_k_trace.tolist(),
        "trace_derivation": {
            "alpha_h_radial": "alpha_h|dR = sqrt|h| * 2 R_Sigma * (R_h^ab q_ab) dR",
            "alpha_K_radial": "alpha_K|dR = sqrt|h| * (R_K^ab q_ab) dR",
            "R_h_trace_values": "alpha_h_radial / (2 R_Sigma sqrt|h|)",
            "R_K_trace_values": "alpha_K_radial / sqrt|h|",
        },
        "trace_provenance": source.get(
            "alpha_radial_component_provenance",
            "active Sigma boundary variation alpha_res radial components",
        ),
    }


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    if input_exists:
        try:
            source = json.loads(input_path.read_text(encoding="utf-8"))
            output = _build_trace_inputs(source)
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-alpha-radial-components-to-trace-residual-inputs-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "trace_residual_inputs_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none"
        if output_written
        else "counterterm_alpha_res_radial_components",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_alpha_h_radial_coefficient_values_from_sigma_boundary_variation",
            "derive_alpha_K_radial_coefficient_values_from_sigma_boundary_variation",
            "provide_R_Sigma_values_and_sqrt_abs_h_values",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Alpha Radial Components To Trace Residual Inputs Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation error", payload["validation_error"]])
    lines.extend(["", "## Next required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
