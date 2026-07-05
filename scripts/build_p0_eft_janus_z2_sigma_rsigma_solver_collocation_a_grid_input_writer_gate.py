from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


Q_INPUT_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/rsigma_a_grid_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_solver_collocation_a_grid_input_writer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_solver_collocation_a_grid_input_writer_gate.json"
)
DEFAULT_A_GRID = [0.25, 0.5, 1.0]


def _reject_forbidden(payload: dict) -> None:
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")


def _load_active_q(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("q_ab input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("q_ab input source must be active_derived")
    _reject_forbidden(payload)
    q = np.asarray(payload.get("unit_intrinsic_metric_q_ab"), dtype=float)
    if q.shape != (3, 3):
        raise ValueError("unit_intrinsic_metric_q_ab must be a 3x3 matrix")
    if not np.all(np.isfinite(q)) or not np.allclose(q, q.T, atol=1e-12):
        raise ValueError("unit_intrinsic_metric_q_ab must be finite and symmetric")
    if abs(float(np.linalg.det(q))) <= 1e-12:
        raise ValueError("unit_intrinsic_metric_q_ab must be nondegenerate")
    return payload


def _validate_grid(grid: list[float]) -> list[float]:
    values = np.asarray(grid, dtype=float)
    if values.ndim != 1 or len(values) < 2:
        raise ValueError("collocation a_grid must be one-dimensional with at least two points")
    if np.any(values <= 0.0) or np.any(np.diff(values) <= 0.0):
        raise ValueError("collocation a_grid must be positive and strictly increasing")
    return values.tolist()


def build_payload(
    *,
    q_input_path: Path = Q_INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
    a_grid: list[float] | None = None,
) -> dict:
    q_input_exists = q_input_path.exists()
    output_written = False
    validation_error = None
    if q_input_exists:
        try:
            _load_active_q(q_input_path)
            grid = _validate_grid(a_grid or DEFAULT_A_GRID)
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
                "archived_z4_background_reuse_used": False,
                "observational_H0_fit_used": False,
                "observational_curvature_fit_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "a_grid": grid,
                "grid_role": "solver_collocation_grid",
                "grid_is_physical_observable": False,
                "grid_is_fit_parameter": False,
                "collocation_policy": "minimal_active_sigma_solver_grid",
                "torsionless_baseline_compatible": True,
                "grid_provenance": (
                    "active q_ab validated; numerical collocation only, not FLRW history"
                ),
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-rsigma-solver-collocation-a-grid-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "q_input_manifest": str(q_input_path),
        "output_manifest": str(output_path),
        "q_input_exists": q_input_exists,
        "rsigma_solver_collocation_a_grid_input_written": output_written,
        "grid_role": "solver_collocation_grid" if output_written else None,
        "grid_is_physical_observable": False,
        "grid_is_fit_parameter": False,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "active_unit_intrinsic_metric_q_ab_inputs",
        "validation_error": validation_error,
        "next_required": [] if output_written else ["derive_unit_intrinsic_metric_q_ab_inputs_json"],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma Solver Collocation a-grid Input Writer Gate",
        "",
        f"q_ab input exists: `{payload['q_input_exists']}`",
        f"Output written: `{payload['rsigma_solver_collocation_a_grid_input_written']}`",
        f"Grid role: `{payload['grid_role']}`",
        f"Physical observable grid: `{payload['grid_is_physical_observable']}`",
        f"Fit parameter grid: `{payload['grid_is_fit_parameter']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
