from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_metric_geometry import normalize_timelike_contravariant_vectors


METRIC_PATH = Path("outputs/active_z2_sigma/sector_metric_on_sigma_inputs.json")
TIME_DIRECTION_PATH = Path("outputs/active_z2_sigma/sector_time_direction_on_sigma_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/sector_four_velocity_on_sigma_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_sector_four_velocity_from_time_direction_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_sector_four_velocity_from_time_direction_gate.json")

FORBIDDEN_FLAGS = [
    "compressed_planck_lcdm_background_used",
    "archived_z4_reuse_used",
    "archived_z4_background_reuse_used",
    "phenomenological_holst_bao_scan_used",
    "observational_H0_fit_used",
    "observational_curvature_fit_used",
]


def _reject_forbidden(payload: dict) -> None:
    for key in FORBIDDEN_FLAGS:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")


def _load_active(path: Path, label: str, ready_key: str) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{label} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{label} source must be active_derived")
    _reject_forbidden(payload)
    if payload.get(ready_key) is not True:
        raise ValueError(f"{ready_key} must be true")
    return payload


def _grid(payload: dict, label: str) -> np.ndarray:
    grid = np.asarray(payload["a_grid"], dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError(f"{label} a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError(f"{label} a_grid must be positive and strictly increasing")
    return grid


def _build_output(metric: dict, time_direction: dict) -> dict:
    grid = _grid(metric, "metric")
    time_grid = _grid(time_direction, "time direction")
    if grid.shape != time_grid.shape or not np.allclose(grid, time_grid, rtol=0.0, atol=0.0):
        raise ValueError("metric and time-direction a_grid must match exactly")
    u_plus = normalize_timelike_contravariant_vectors(
        metric["metric_plus_munu_values"],
        time_direction["time_direction_plus_values"],
    )
    u_minus = normalize_timelike_contravariant_vectors(
        metric["metric_minus_munu_values"],
        time_direction["time_direction_minus_values"],
    )
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "sector_four_velocity_on_sigma_ready": True,
        "a_grid": grid.tolist(),
        "u_plus_contravariant_values": u_plus,
        "u_minus_contravariant_values": u_minus,
        "normalization": "g_munu u^mu u^nu = -1",
        "velocity_source": str(TIME_DIRECTION_PATH),
        "metric_source": str(METRIC_PATH),
    }


def build_payload(
    *,
    metric_path: Path = METRIC_PATH,
    time_direction_path: Path = TIME_DIRECTION_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = {
        "sector_metric_on_sigma_inputs": metric_path.exists(),
        "sector_time_direction_on_sigma_inputs": time_direction_path.exists(),
    }
    output_written = False
    validation_error = None
    if all(input_exists.values()):
        try:
            output = _build_output(
                _load_active(metric_path, "metric", "sector_metric_on_sigma_ready"),
                _load_active(time_direction_path, "time direction", "sector_time_direction_on_sigma_ready"),
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    missing = [key for key, exists in input_exists.items() if not exists]
    return {
        "status": "janus-z2-sigma-sector-four-velocity-from-time-direction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "output_manifest": str(output_path),
        "sector_four_velocity_on_sigma_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else (missing[0] if missing else "sector_four_velocity_validation"),
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_sector_metric_on_sigma_inputs",
            "derive_sector_time_direction_on_sigma_inputs",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Sector Four-Velocity From Time Direction Gate",
        "",
        f"Output written: `{payload['sector_four_velocity_on_sigma_written']}`",
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
