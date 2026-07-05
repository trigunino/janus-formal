from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


DENSITY_PRESSURE_PATH = Path("outputs/active_z2_sigma/sector_density_pressure_on_sigma_inputs.json")
METRIC_PATH = Path("outputs/active_z2_sigma/sector_metric_on_sigma_inputs.json")
VELOCITY_PATH = Path("outputs/active_z2_sigma/sector_four_velocity_on_sigma_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/sector_perfect_fluid_on_sigma_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_sector_perfect_fluid_on_sigma_input_writer_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_sector_perfect_fluid_on_sigma_input_writer_gate.json")

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
    values = np.asarray(payload["a_grid"], dtype=float)
    if values.ndim != 1 or len(values) < 2:
        raise ValueError(f"{label} a_grid must be one-dimensional with at least two points")
    if np.any(values <= 0.0) or np.any(np.diff(values) <= 0.0):
        raise ValueError(f"{label} a_grid must be positive and strictly increasing")
    return values


def _aligned(reference: np.ndarray, payload: dict, label: str) -> None:
    values = _grid(payload, label)
    if values.shape != reference.shape or not np.allclose(values, reference, rtol=0.0, atol=0.0):
        raise ValueError(f"{label} a_grid must match density/pressure a_grid exactly")


def _array(payload: dict, key: str, shape: tuple[int, ...]) -> list:
    values = np.asarray(payload[key], dtype=float)
    if values.shape != shape or not np.all(np.isfinite(values)):
        raise ValueError(f"{key} must be finite with shape {shape}")
    return values.tolist()


def _build_output(density_pressure: dict, metric: dict, velocity: dict) -> dict:
    grid = _grid(density_pressure, "density/pressure")
    _aligned(grid, metric, "metric")
    _aligned(grid, velocity, "velocity")
    n_grid = len(grid)
    metric_plus = np.asarray(metric["metric_plus_munu_values"], dtype=float)
    if metric_plus.ndim != 3 or metric_plus.shape[0] != n_grid or metric_plus.shape[1] != metric_plus.shape[2]:
        raise ValueError("metric_plus_munu_values must have shape [len(a_grid), dim, dim]")
    dim = metric_plus.shape[1]
    metric_minus = np.asarray(metric["metric_minus_munu_values"], dtype=float)
    if metric_minus.shape != metric_plus.shape:
        raise ValueError("metric_minus_munu_values must match metric_plus_munu_values shape")
    for item in list(metric_plus) + list(metric_minus):
        if not np.allclose(item, item.T):
            raise ValueError("metric tensors must be symmetric")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "sector_perfect_fluid_on_sigma_ready": True,
        "a_grid": grid.tolist(),
        "rho_plus_values": _array(density_pressure, "rho_plus_values", (n_grid,)),
        "p_plus_values": _array(density_pressure, "p_plus_values", (n_grid,)),
        "rho_minus_values": _array(density_pressure, "rho_minus_values", (n_grid,)),
        "p_minus_values": _array(density_pressure, "p_minus_values", (n_grid,)),
        "metric_plus_munu_values": _array(metric, "metric_plus_munu_values", (n_grid, dim, dim)),
        "metric_minus_munu_values": _array(metric, "metric_minus_munu_values", (n_grid, dim, dim)),
        "u_plus_contravariant_values": _array(velocity, "u_plus_contravariant_values", (n_grid, dim)),
        "u_minus_contravariant_values": _array(velocity, "u_minus_contravariant_values", (n_grid, dim)),
        "density_pressure_source": str(DENSITY_PRESSURE_PATH),
        "metric_source": str(METRIC_PATH),
        "velocity_source": str(VELOCITY_PATH),
    }


def build_payload(
    *,
    density_pressure_path: Path = DENSITY_PRESSURE_PATH,
    metric_path: Path = METRIC_PATH,
    velocity_path: Path = VELOCITY_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = {
        "sector_density_pressure_on_sigma_inputs": density_pressure_path.exists(),
        "sector_metric_on_sigma_inputs": metric_path.exists(),
        "sector_four_velocity_on_sigma_inputs": velocity_path.exists(),
    }
    output_written = False
    validation_error = None
    if all(input_exists.values()):
        try:
            output = _build_output(
                _load_active(density_pressure_path, "density/pressure", "sector_density_pressure_on_sigma_ready"),
                _load_active(metric_path, "metric", "sector_metric_on_sigma_ready"),
                _load_active(velocity_path, "velocity", "sector_four_velocity_on_sigma_ready"),
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    missing = [key for key, exists in input_exists.items() if not exists]
    return {
        "status": "janus-z2-sigma-sector-perfect-fluid-on-sigma-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "output_manifest": str(output_path),
        "sector_perfect_fluid_on_sigma_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else (missing[0] if missing else "sector_perfect_fluid_validation"),
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_sector_density_pressure_on_sigma_inputs",
            "derive_sector_metric_on_sigma_inputs",
            "derive_sector_four_velocity_on_sigma_inputs",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Sector Perfect Fluid On Sigma Input Writer Gate",
        "",
        f"Output written: `{payload['sector_perfect_fluid_on_sigma_written']}`",
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
