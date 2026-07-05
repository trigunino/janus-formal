from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


Q_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
GRID_PATH = Path("outputs/active_z2_sigma/rsigma_a_grid_inputs.json")
METRIC_OUTPUT_PATH = Path("outputs/active_z2_sigma/sector_metric_on_sigma_inputs.json")
TIME_OUTPUT_PATH = Path("outputs/active_z2_sigma/sector_time_direction_on_sigma_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_sector_metric_time_direction_from_unit_throat_chart_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_sector_metric_time_direction_from_unit_throat_chart_gate.json")

FORBIDDEN_FLAGS = [
    "compressed_planck_lcdm_background_used",
    "archived_z4_reuse_used",
    "archived_z4_background_reuse_used",
    "phenomenological_holst_bao_scan_used",
    "observational_H0_fit_used",
    "observational_curvature_fit_used",
]


def _load_active(path: Path, label: str) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{label} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{label} source must be active_derived")
    for key in FORBIDDEN_FLAGS:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    return payload


def _build_outputs(q_payload: dict, grid_payload: dict) -> tuple[dict, dict]:
    q = np.asarray(q_payload["unit_intrinsic_metric_q_ab"], dtype=float)
    if q.ndim != 2 or q.shape[0] != q.shape[1] or not np.allclose(q, q.T):
        raise ValueError("unit_intrinsic_metric_q_ab must be symmetric square")
    if not np.all(np.linalg.eigvalsh(q) > 0.0):
        raise ValueError("unit_intrinsic_metric_q_ab must be positive definite")
    grid = np.asarray(grid_payload["a_grid"], dtype=float)
    if grid.ndim != 1 or len(grid) < 2 or np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    dim = q.shape[0] + 2
    metric = np.zeros((dim, dim), dtype=float)
    metric[0, 0] = -1.0
    metric[1 : 1 + q.shape[0], 1 : 1 + q.shape[0]] = q
    metric[-1, -1] = 1.0
    time = [1.0] + [0.0] * (dim - 1)
    common = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "a_grid": grid.tolist(),
        "chart": "unit_orthonormal_throat_chart",
    }
    metric_payload = {
        **common,
        "sector_metric_on_sigma_ready": True,
        "metric_plus_munu_values": [metric.tolist() for _ in grid],
        "metric_minus_munu_values": [metric.tolist() for _ in grid],
        "metric_formula": "diag(-1, q_ab, +1_normal) in active unit collar chart",
    }
    time_payload = {
        **common,
        "sector_time_direction_on_sigma_ready": True,
        "time_direction_plus_values": [time for _ in grid],
        "time_direction_minus_values": [time for _ in grid],
        "time_direction_formula": "unit collar chart time vector before normalization",
    }
    return metric_payload, time_payload


def build_payload(
    *,
    q_path: Path = Q_PATH,
    grid_path: Path = GRID_PATH,
    metric_output_path: Path = METRIC_OUTPUT_PATH,
    time_output_path: Path = TIME_OUTPUT_PATH,
) -> dict:
    input_exists = {
        "unit_intrinsic_metric_q_ab_inputs": q_path.exists(),
        "rsigma_a_grid_inputs": grid_path.exists(),
    }
    output_written = False
    validation_error = None
    if all(input_exists.values()):
        try:
            metric, time = _build_outputs(_load_active(q_path, "q_ab"), _load_active(grid_path, "a_grid"))
            metric_output_path.parent.mkdir(parents=True, exist_ok=True)
            metric_output_path.write_text(json.dumps(metric, indent=2), encoding="utf-8")
            time_output_path.write_text(json.dumps(time, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    missing = [key for key, exists in input_exists.items() if not exists]
    return {
        "status": "janus-z2-sigma-sector-metric-time-direction-from-unit-throat-chart-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "metric_output_manifest": str(metric_output_path),
        "time_direction_output_manifest": str(time_output_path),
        "outputs_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else (missing[0] if missing else "unit_throat_chart_validation"),
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "derive_unit_intrinsic_metric_q_ab_inputs",
            "derive_active_a_grid_inputs",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Sector Metric/Time Direction From Unit Throat Chart Gate",
        "",
        f"Outputs written: `{payload['outputs_written']}`",
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
