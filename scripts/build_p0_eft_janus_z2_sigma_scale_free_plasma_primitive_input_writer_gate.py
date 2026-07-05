from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_active_inputs import (
    load_active_z2sigma_scale_free_plasma_primitive_inputs,
    write_active_z2sigma_scale_free_plasma_primitive_manifest,
)


INPUT_PATH = Path("outputs/active_z2_sigma/bao_scale_free_plasma_primitive_normalization_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/bao_scale_free_plasma_primitive_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_scale_free_plasma_primitive_input_writer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_scale_free_plasma_primitive_input_writer_gate.json"
)


def _grid_function(z_grid: np.ndarray, values: np.ndarray):
    def function(z):
        return np.interp(np.asarray(z, dtype=float), z_grid, values)

    return function


def _build_output(input_path: Path, output_path: Path) -> Path:
    payload = json.loads(input_path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input source must be active_derived")
    for key in [
        "compressed_planck_lcdm_rd_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    z_grid = np.asarray(payload["z_grid"], dtype=float)
    cs = np.asarray(payload["c_s_over_c_Z2Sigma"], dtype=float)
    gamma = np.asarray(payload["Gamma_drag_over_H0_Z2Sigma"], dtype=float)
    if z_grid.ndim != 1 or len(z_grid) < 2 or np.any(np.diff(z_grid) <= 0.0):
        raise ValueError("z_grid must be one-dimensional and strictly increasing")
    if cs.shape != z_grid.shape or gamma.shape != z_grid.shape:
        raise ValueError("Primitive arrays must align with z_grid")
    if np.any(cs <= 0.0) or np.any(gamma <= 0.0):
        raise ValueError("Primitive values must be positive")
    return write_active_z2sigma_scale_free_plasma_primitive_manifest(
        output_path,
        z_grid,
        _grid_function(z_grid, cs),
        _grid_function(z_grid, gamma),
        float(payload.get("z_max", z_grid[-1])),
        primitive_provenance=payload.get("primitive_provenance", {}),
        z_d_bracket=payload.get("z_d_bracket"),
    )


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    written = False
    valid = False
    validation_error = None
    z_grid_length = None
    if input_exists:
        try:
            path = _build_output(input_path, output_path)
            written = True
            primitive = load_active_z2sigma_scale_free_plasma_primitive_inputs(path)
            valid = True
            z_grid_length = int(len(primitive.z_grid))
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-scale-free-plasma-primitive-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "plasma_primitive_written": written,
        "plasma_primitive_valid": valid,
        "z_grid_length": z_grid_length,
        "uses_compressed_planck_lcdm_rd": False,
        "uses_archived_z4": False,
        "uses_observational_H0_fit": False,
        "gate_passed": valid,
        "validation_error": validation_error,
        "next_required": [
            "derive_active_c_s_over_c_Z2Sigma_of_z",
            "derive_active_Gamma_drag_over_H0_Z2Sigma_of_z",
            "supply_outputs_active_z2_sigma_bao_scale_free_plasma_primitive_normalization_inputs_json",
            "merge_background_and_plasma_primitives",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Scale-Free Plasma Primitive Input Writer Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Plasma primitive written: `{payload['plasma_primitive_written']}`",
        f"Plasma primitive valid: `{payload['plasma_primitive_valid']}`",
        f"Gate passed: `{payload['gate_passed']}`",
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
