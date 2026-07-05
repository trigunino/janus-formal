from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_rsigma_radial_terms import (
    build_active_z2sigma_rsigma_radial_term_payload,
    write_active_z2sigma_rsigma_radial_term_manifest,
)


INPUT_PATH = Path("outputs/active_z2_sigma/counterterm_radial_density_variation_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/rsigma_E_counterterm.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_counterterm_radial_term_from_density_variation_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_counterterm_radial_term_from_density_variation_gate.json"
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


def _load_input(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("counterterm density input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("counterterm density input source must be active_derived")
    _reject_forbidden(payload)
    if payload.get("counterterm_density_explicit") is not True:
        raise ValueError("counterterm_density_explicit must be true")
    if payload.get("radial_variation_ready") is not True:
        raise ValueError("radial_variation_ready must be true")
    for key in [
        "a_grid",
        "sqrt_abs_h_values",
        "partial_R_sqrt_abs_h_values",
        "L_ct_values",
        "partial_R_L_ct_values",
    ]:
        if key not in payload:
            raise ValueError(f"counterterm density input missing {key}")
    return payload


def _aligned_array(payload: dict, key: str, shape: tuple[int, ...]) -> np.ndarray:
    values = np.asarray(payload[key], dtype=float)
    if values.shape != shape or not np.all(np.isfinite(values)):
        raise ValueError(f"{key} must be finite and aligned with a_grid")
    return values


def _compute_term(payload: dict) -> tuple[list[float], list[float]]:
    grid = np.asarray(payload["a_grid"], dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    shape = grid.shape
    sqrt_h = _aligned_array(payload, "sqrt_abs_h_values", shape)
    partial_sqrt_h = _aligned_array(payload, "partial_R_sqrt_abs_h_values", shape)
    L_ct = _aligned_array(payload, "L_ct_values", shape)
    partial_L_ct = _aligned_array(payload, "partial_R_L_ct_values", shape)
    if np.any(sqrt_h <= 0.0):
        raise ValueError("sqrt_abs_h_values must be positive")
    term = partial_sqrt_h * L_ct + sqrt_h * partial_L_ct
    return grid.tolist(), term.tolist()


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
            source = _load_input(input_path)
            a_grid, term_values = _compute_term(source)
            term = build_active_z2sigma_rsigma_radial_term_payload(
                term_name="E_counterterm",
                a_grid=a_grid,
                term_values=term_values,
                term_provenance=(
                    "active radial variation of sqrt_abs_h * L_ct with explicit density"
                ),
            )
            write_active_z2sigma_rsigma_radial_term_manifest(output_path, term)
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-rsigma-counterterm-radial-term-from-density-variation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "E_counterterm_from_density_variation_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "counterterm_radial_density_variation_inputs",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_explicit_L_ct_density",
            "derive_sqrt_abs_h_and_partial_R_sqrt_abs_h_on_Sigma",
            "derive_partial_R_L_ct_from_active_h_K_torsion_fields",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma Counterterm Radial Term From Density Variation Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Output written: `{payload['E_counterterm_from_density_variation_written']}`",
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
