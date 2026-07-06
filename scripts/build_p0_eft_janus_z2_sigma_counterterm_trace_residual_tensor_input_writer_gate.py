from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


Q_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
TRACE_PATH = Path("outputs/active_z2_sigma/counterterm_trace_residual_inputs.json")
METRIC_OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_metric_residual_tensor_inputs.json")
EXTRINSIC_OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_extrinsic_residual_tensor_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_trace_residual_tensor_input_writer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_trace_residual_tensor_input_writer_gate.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


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
        raise ValueError(f"{key} must be finite and aligned with a_grid")
    return values


def _build_tensors(q_payload: dict, trace_payload: dict) -> tuple[dict, dict]:
    _active(q_payload, "q_payload")
    _active(trace_payload, "trace_payload")
    q = np.asarray(q_payload["unit_intrinsic_metric_q_ab"], dtype=float)
    if q.ndim != 2 or q.shape[0] != q.shape[1] or not np.all(np.isfinite(q)):
        raise ValueError("unit_intrinsic_metric_q_ab must be a finite square tensor")
    dim = q.shape[0]
    q_inv = np.linalg.inv(q)
    a_grid = np.asarray(trace_payload["a_grid"], dtype=float)
    if a_grid.ndim != 1 or a_grid.size < 1 or np.any(a_grid <= 0.0):
        raise ValueError("a_grid must be a positive one-dimensional array")
    r_h_trace = _series(trace_payload, "R_h_trace_values", a_grid.shape)
    r_k_trace = _series(trace_payload, "R_K_trace_values", a_grid.shape)
    r_h = np.asarray([(value / dim) * q_inv for value in r_h_trace], dtype=float)
    r_k = np.asarray([(value / dim) * q_inv for value in r_k_trace], dtype=float)
    common = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "a_grid": a_grid.tolist(),
        "intrinsic_dimension": dim,
        "tensor_reconstruction": "round_throat_isotropic_trace_reduction",
        "formula": "R^{ab} = (R_trace/d) q^{ab}",
    }
    metric = {
        **common,
        "R_h_ab": r_h.tolist(),
        "R_h_trace_values": r_h_trace.tolist(),
    }
    extrinsic = {
        **common,
        "R_K_ab": r_k.tolist(),
        "R_K_trace_values": r_k_trace.tolist(),
    }
    return metric, extrinsic


def build_payload(
    *,
    q_path: Path = Q_PATH,
    trace_path: Path = TRACE_PATH,
    metric_output_path: Path = METRIC_OUTPUT_PATH,
    extrinsic_output_path: Path = EXTRINSIC_OUTPUT_PATH,
) -> dict:
    input_exists = {
        "unit_intrinsic_metric_q_ab": q_path.exists(),
        "counterterm_trace_residual_inputs": trace_path.exists(),
    }
    output_written = False
    validation_error = None
    if all(input_exists.values()):
        try:
            metric, extrinsic = _build_tensors(_load(q_path), _load(trace_path))
            metric_output_path.parent.mkdir(parents=True, exist_ok=True)
            metric_output_path.write_text(json.dumps(metric, indent=2), encoding="utf-8")
            extrinsic_output_path.write_text(json.dumps(extrinsic, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-counterterm-trace-residual-tensor-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "metric_output_manifest": str(metric_output_path),
        "extrinsic_output_manifest": str(extrinsic_output_path),
        "round_throat_trace_to_tensor_formula": "R^{ab} = (R_trace/d) q^{ab}",
        "writes_full_tensor_inputs": output_written,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "primary_blocker": "none"
        if output_written
        else next((name for name, exists in input_exists.items() if not exists), "invalid_inputs"),
        "next_required": []
        if output_written
        else [name for name, exists in input_exists.items() if not exists],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Trace Residual Tensor Input Writer Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        f"Formula: `{payload['round_throat_trace_to_tensor_formula']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
