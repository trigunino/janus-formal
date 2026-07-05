from __future__ import annotations

import json
from pathlib import Path

import numpy as np


METRIC_RESIDUAL_INPUT_PATH = Path(
    "outputs/active_z2_sigma/counterterm_metric_residual_tensor_inputs.json"
)
COFRAME_TRACE_INPUT_PATH = Path("outputs/active_z2_sigma/counterterm_coframe_trace_inputs.json")
OUTPUT_PATH = Path(
    "outputs/active_z2_sigma/counterterm_tetrad_metric_residual_coefficient_inputs.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_metric_residual_coefficient_input_writer_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_tetrad_metric_residual_coefficient_input_writer_gate.json"
)


FORBIDDEN_FLAGS = [
    "compressed_planck_lcdm_background_used",
    "archived_z4_reuse_used",
    "phenomenological_holst_bao_scan_used",
    "fitted_counterterm_coefficient_used",
]


def _load_active(path: Path, *, array_key: str) -> tuple[dict | None, str | None]:
    if not path.exists():
        return None, None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        if payload.get("active_core") != "Z2_tunnel_Sigma":
            raise ValueError("active_core must be Z2_tunnel_Sigma")
        if payload.get("source") != "active_derived":
            raise ValueError("source must be active_derived")
        for flag in FORBIDDEN_FLAGS:
            if payload.get(flag) is not False:
                raise ValueError(f"Forbidden provenance flag must be false: {flag}")
        if array_key not in payload:
            raise ValueError(f"Missing array field: {array_key}")
        if not isinstance(payload.get("provenance"), str) or not payload["provenance"].strip():
            raise ValueError("provenance must be nonempty")
        return payload, None
    except Exception as exc:
        return None, str(exc)


def _compute_re_metric(metric_payload: dict, coframe_payload: dict) -> list[list[float]]:
    r_h = np.asarray(metric_payload["R_h_ab"], dtype=float)
    e_bI = np.asarray(coframe_payload["e_bI_on_Sigma"], dtype=float)
    eta = np.asarray(
        coframe_payload.get("eta_IJ", np.eye(e_bI.shape[1]).tolist()),
        dtype=float,
    )
    if r_h.ndim != 2 or r_h.shape[0] != r_h.shape[1]:
        raise ValueError("R_h_ab must be a square 2D tensor")
    if e_bI.ndim != 2 or e_bI.shape[0] != r_h.shape[1]:
        raise ValueError("e_bI_on_Sigma must have one row per boundary index b")
    if eta.shape != (e_bI.shape[1], e_bI.shape[1]):
        raise ValueError("eta_IJ shape must match the internal coframe dimension")
    if not np.isfinite(r_h).all() or not np.isfinite(e_bI).all() or not np.isfinite(eta).all():
        raise ValueError("counterterm tetrad metric residual inputs must be finite")
    return (2.0 * r_h @ e_bI @ eta.T).tolist()


def build_payload(
    *,
    metric_residual_input_path: Path = METRIC_RESIDUAL_INPUT_PATH,
    coframe_trace_input_path: Path = COFRAME_TRACE_INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    metric_payload, metric_error = _load_active(metric_residual_input_path, array_key="R_h_ab")
    coframe_payload, coframe_error = _load_active(coframe_trace_input_path, array_key="e_bI_on_Sigma")
    output_written = False
    write_error = None
    coefficient = None
    if metric_payload is not None and coframe_payload is not None:
        try:
            coefficient = _compute_re_metric(metric_payload, coframe_payload)
            output = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "fitted_counterterm_coefficient_used": False,
                "formula": (
                    "R_e_metric^{aI} = 2 R_h^{ab} eta^{IJ} e_bJ "
                    "when R_h^{ab} is symmetric"
                ),
                "R_e_metric_aI": coefficient,
                "metric_residual_provenance": metric_payload.get("provenance", "active_metric_residual"),
                "coframe_trace_provenance": coframe_payload.get("provenance", "active_coframe_trace"),
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            write_error = str(exc)
    return {
        "status": "janus-z2-sigma-counterterm-tetrad-metric-residual-coefficient-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "metric_residual_input": str(metric_residual_input_path),
        "coframe_trace_input": str(coframe_trace_input_path),
        "output_manifest": str(output_path),
        "metric_residual_input_exists": metric_residual_input_path.exists(),
        "coframe_trace_input_exists": coframe_trace_input_path.exists(),
        "metric_residual_input_valid": metric_payload is not None,
        "coframe_trace_input_valid": coframe_payload is not None,
        "metric_residual_validation_error": metric_error,
        "coframe_trace_validation_error": coframe_error,
        "tetrad_metric_residual_coefficient_formula_declared": True,
        "tetrad_metric_residual_coefficient_value_ready": output_written,
        "coefficient_output_written": output_written,
        "coefficient_preview": coefficient,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "uses_fitted_counterterm_coefficient": False,
        "gate_passed": output_written,
        "validation_error": write_error,
        "nearest_frontier": {
            "blocks": [
                key
                for key, ready in {
                    "active_metric_residual_tensor_R_h_ab": metric_payload is not None,
                    "active_coframe_trace_e_bI_on_Sigma": coframe_payload is not None,
                }.items()
                if not ready
            ],
            "diagnostic_only": True,
        },
        "next_required": [
            "derive_active_metric_residual_tensor_R_h_ab",
            "derive_active_coframe_trace_e_bI_on_Sigma",
            "rerun_counterterm_tetrad_residual_channel_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Tetrad Metric Residual Coefficient Input Writer Gate",
        "",
        f"Metric residual valid: `{payload['metric_residual_input_valid']}`",
        f"Coframe trace valid: `{payload['coframe_trace_input_valid']}`",
        f"Coefficient written: `{payload['coefficient_output_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
