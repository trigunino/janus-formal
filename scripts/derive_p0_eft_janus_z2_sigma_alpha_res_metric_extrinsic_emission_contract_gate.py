from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_trace_residual_tensor_input_writer_gate import (
    build_payload as build_trace_tensor_writer,
)
from scripts.derive_p0_eft_janus_z2_sigma_non_ghy_rh_rk_elimination_decision_gate import (
    build_payload as build_elimination_decision,
)


TRACE_PATH = Path("outputs/active_z2_sigma/counterterm_trace_residual_inputs.json")
Q_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
METRIC_OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_metric_residual_tensor_inputs.json")
EXTRINSIC_OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_extrinsic_residual_tensor_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_alpha_res_metric_extrinsic_emission_contract_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_alpha_res_metric_extrinsic_emission_contract_gate.json"
)


def _trace_status(path: Path) -> dict:
    if not path.exists():
        return {
            "exists": False,
            "has_R_h_trace_values": False,
            "has_R_K_trace_values": False,
            "validation_error": None,
        }
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        return {
            "exists": True,
            "has_R_h_trace_values": "R_h_trace_values" in payload,
            "has_R_K_trace_values": "R_K_trace_values" in payload,
            "validation_error": None,
        }
    except Exception as exc:
        return {
            "exists": True,
            "has_R_h_trace_values": False,
            "has_R_K_trace_values": False,
            "validation_error": str(exc),
        }


def build_payload(
    *,
    trace_path: Path = TRACE_PATH,
    q_path: Path = Q_PATH,
    metric_output_path: Path = METRIC_OUTPUT_PATH,
    extrinsic_output_path: Path = EXTRINSIC_OUTPUT_PATH,
) -> dict:
    trace = _trace_status(trace_path)
    writer = build_trace_tensor_writer(
        q_path=q_path,
        trace_path=trace_path,
        metric_output_path=metric_output_path,
        extrinsic_output_path=extrinsic_output_path,
    )
    decision = build_elimination_decision()
    trace_ready = bool(
        trace["exists"]
        and trace["has_R_h_trace_values"]
        and trace["has_R_K_trace_values"]
        and trace["validation_error"] is None
    )
    values_emitted = bool(writer["gate_passed"])
    return {
        "status": "janus-z2-sigma-alpha-res-metric-extrinsic-emission-contract-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_emission_contract",
        "contract": {
            "input_manifest": str(trace_path),
            "required_fields": [
                "a_grid",
                "R_h_trace_values",
                "R_K_trace_values",
            ],
            "round_throat_reconstruction": "R_h^ab=(R_h_trace/d)q^ab; R_K^ab=(R_K_trace/d)q^ab",
            "downstream_metric_tensor_manifest": writer["metric_output_manifest"],
            "downstream_extrinsic_tensor_manifest": writer["extrinsic_output_manifest"],
        },
        "trace_input_status": trace,
        "trace_values_ready": trace_ready,
        "R_h_ab_emitted": values_emitted,
        "R_K_ab_emitted": values_emitted,
        "writer_gate": {
            "gate": writer["status"],
            "passed": writer["gate_passed"],
            "primary_blocker": writer["primary_blocker"],
            "validation_error": writer["validation_error"],
        },
        "elimination_decision": {
            "gate": decision["status"],
            "decision": decision["decision"],
            "primary_blocker": decision["primary_blocker"],
        },
        "gate_passed": values_emitted,
        "primary_blocker": "none"
        if values_emitted
        else "counterterm_trace_residual_inputs_from_sigma_boundary_variation",
        "next_required": []
        if values_emitted
        else [
            "derive_R_h_trace_values_from_metric_alpha_res_component",
            "derive_R_K_trace_values_from_extrinsic_alpha_res_component",
            "write_counterterm_trace_residual_inputs_json",
        ],
        "forbidden_shortcuts": [
            "do_not_fill_R_h_trace_values_by_fit",
            "do_not_fill_R_K_trace_values_by_linear_K_duplicate",
            "do_not_emit_zero_traces_without_non_GHY_absence_proof",
        ],
        "verdict": (
            "The emission interface is now precise. The repo can turn active trace "
            "values into R_h_ab/R_K_ab tensors, but the trace values themselves must "
            "come from the Sigma boundary variation."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Alpha_res Metric/Extrinsic Emission Contract Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        f"R_h emitted: `{payload['R_h_ab_emitted']}`",
        f"R_K emitted: `{payload['R_K_ab_emitted']}`",
        "",
        payload["verdict"],
        "",
        "## Next required",
    ]
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
