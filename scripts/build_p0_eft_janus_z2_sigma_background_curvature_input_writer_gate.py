from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_background_inputs import build_active_z2sigma_background_scalar_payload
from scripts.build_p0_eft_janus_z2_sigma_active_flrw_spatial_metric_branch_gate import (
    build_payload as build_active_flrw_spatial_metric_branch_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_curvature_normalization_from_branch_gate import (
    build_payload as build_curvature_normalization_from_branch_payload,
)


INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_normalization_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_background_curvature_input_writer_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_background_curvature_input_writer_gate.json")


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    branch = build_active_flrw_spatial_metric_branch_payload()
    normalization_from_branch = build_curvature_normalization_from_branch_payload()
    input_exists = input_path.exists()
    output_written = False
    validation_error = None
    if input_exists:
        try:
            built = build_active_z2sigma_background_scalar_payload(
                json.loads(input_path.read_text(encoding="utf-8")),
                "omega_k_Z2Sigma",
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(built, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-background-curvature-input-writer-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "background_curvature_input_written": output_written,
        "projective_tunnel_two_fold_topology_ready": True,
        "topology_alone_fixes_numeric_omega_k": False,
        "active_FLRW_spatial_metric_branch_gate_passed": branch["gate_passed"],
        "active_FLRW_spatial_metric_branch_values_ready": branch[
            "flrw_spatial_metric_branch_values_ready"
        ],
        "curvature_normalization_from_branch_gate_passed": normalization_from_branch[
            "gate_passed"
        ],
        "computes_omega_k_from_k_Rcurv_H0": normalization_from_branch[
            "computes_omega_k_from_k_Rcurv_H0"
        ],
        "requires_active_FLRW_curvature_radius_or_embedding_scale": True,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_H0_fit": False,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "run_background_curvature_normalization_from_branch_gate",
            "close_active_FLRW_spatial_metric_branch_gate",
            "derive_active_FLRW_curvature_radius_or_embedding_scale",
            "supply_outputs_active_z2_sigma_background_curvature_normalization_inputs_json",
            "run_background_scalar_inputs_assembler_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Z2/Sigma Background Curvature Input Writer Gate",
            "",
            f"Input exists: `{payload['input_exists']}`",
            f"Curvature input written: `{payload['background_curvature_input_written']}`",
            f"Gate passed: `{payload['gate_passed']}`",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
