from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_background_curvature_radius_input_writer_gate import (
    build_payload as build_radius_input,
)
from scripts.build_p0_eft_janus_z2_sigma_background_h0_input_writer_gate import (
    build_payload as build_h0_input,
)
from scripts.build_p0_eft_janus_z2_sigma_h0_radius_to_scale_free_omega_k_pipeline_gate import (
    build_payload as build_h0_radius_pipeline,
)


H0_NORM_PATH = Path("outputs/active_z2_sigma/background_H0_normalization_inputs.json")
RADIUS_NORM_PATH = Path(
    "outputs/active_z2_sigma/background_curvature_radius_normalization_inputs.json"
)
H0_INPUT_PATH = Path("outputs/active_z2_sigma/background_H0_inputs.json")
RADIUS_INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_radius_inputs.json")
SIGN_INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_sign_inputs.json")
SCALE_NORM_PATH = Path(
    "outputs/active_z2_sigma/background_dimensionless_curvature_scale_normalization_inputs.json"
)
SCALE_INPUT_PATH = Path("outputs/active_z2_sigma/background_dimensionless_curvature_scale_inputs.json")
OMEGA_OUTPUT_PATH = Path("outputs/active_z2_sigma/background_scale_free_omega_k_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_dimensional_anchor_pipeline_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_dimensional_anchor_pipeline_gate.json"
)


def build_payload(
    *,
    h0_norm_path: Path = H0_NORM_PATH,
    radius_norm_path: Path = RADIUS_NORM_PATH,
    h0_input_path: Path = H0_INPUT_PATH,
    radius_input_path: Path = RADIUS_INPUT_PATH,
    sign_input_path: Path = SIGN_INPUT_PATH,
    scale_norm_path: Path = SCALE_NORM_PATH,
    scale_input_path: Path = SCALE_INPUT_PATH,
    omega_output_path: Path = OMEGA_OUTPUT_PATH,
) -> dict:
    h0 = build_h0_input(input_path=h0_norm_path, output_path=h0_input_path)
    radius = build_radius_input(input_path=radius_norm_path, output_path=radius_input_path)
    omega = build_h0_radius_pipeline(
        h0_input_path=h0_input_path,
        radius_input_path=radius_input_path,
        sign_input_path=sign_input_path,
        scale_normalization_path=scale_norm_path,
        scale_input_path=scale_input_path,
        omega_k_output_path=omega_output_path,
    )
    stages = {
        "h0_input": h0["gate_passed"],
        "curvature_radius_input": radius["gate_passed"],
        "scale_free_omega_k": omega["gate_passed"],
    }
    return {
        "status": "janus-z2-sigma-effective-dimensional-anchor-pipeline-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "effective_initial_state",
        "stages": stages,
        "stage_payloads": {
            "h0_input": h0,
            "curvature_radius_input": radius,
            "scale_free_omega_k": omega,
        },
        "pipeline_ready": all(stages.values()),
        "full_no_fit_prediction_ready": False,
        "primary_blocker": "none"
        if all(stages.values())
        else next(name for name, ready in stages.items() if not ready),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Effective Dimensional Anchor Pipeline Gate",
        "",
        f"Pipeline ready: `{payload['pipeline_ready']}`",
        f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Stages",
    ]
    lines.extend(f"- `{name}`: `{ready}`" for name, ready in payload["stages"].items())
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
