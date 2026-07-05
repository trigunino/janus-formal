from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_background_inputs import (
    build_active_z2sigma_curvature_payload_from_flrw_branch,
)
from scripts.build_p0_eft_janus_z2_sigma_active_flrw_spatial_metric_branch_gate import (
    build_payload as build_active_flrw_spatial_metric_branch_payload,
)


INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_branch_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_normalization_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_background_curvature_normalization_from_branch_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_background_curvature_normalization_from_branch_gate.json")


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    branch = build_active_flrw_spatial_metric_branch_payload()
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    omega_k_value = None
    if input_exists:
        try:
            built = build_active_z2sigma_curvature_payload_from_flrw_branch(
                json.loads(input_path.read_text(encoding="utf-8"))
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(built, indent=2), encoding="utf-8")
            omega_k_value = built["scalars"]["omega_k_Z2Sigma"]
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-background-curvature-normalization-from-branch-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "background_curvature_normalization_input_written": output_written,
        "active_FLRW_spatial_metric_branch_gate_passed": branch["gate_passed"],
        "active_FLRW_spatial_metric_branch_values_ready": branch[
            "flrw_spatial_metric_branch_values_ready"
        ],
        "computes_omega_k_from_k_Rcurv_H0": True,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_curvature_fit": False,
        "uses_observational_H0_fit": False,
        "omega_k_Z2Sigma_value": omega_k_value,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "derive_active_FLRW_spatial_metric_branch_values",
            "supply_outputs_active_z2_sigma_background_curvature_branch_inputs_json",
            "run_background_curvature_input_writer_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Background Curvature Normalization From Branch Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Computes omega_k: `{payload['computes_omega_k_from_k_Rcurv_H0']}`",
        f"Normalization input written: `{payload['background_curvature_normalization_input_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
