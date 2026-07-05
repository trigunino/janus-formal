from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_flrw_to_scale_free_background_primitive_gate import (
    build_payload as build_background_primitive_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_h0_radius_to_scale_free_omega_k_pipeline_gate import (
    build_payload as build_omega_k_payload,
)


H0_INPUT_PATH = Path("outputs/active_z2_sigma/background_H0_inputs.json")
RADIUS_INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_radius_inputs.json")
SIGN_INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_sign_inputs.json")
FLRW_COMPONENT_PATH = Path("outputs/active_z2_sigma/flrw_components.json")
OMEGA_K_OUTPUT_PATH = Path("outputs/active_z2_sigma/background_scale_free_omega_k_inputs.json")
BACKGROUND_PRIMITIVE_PATH = Path(
    "outputs/active_z2_sigma/bao_scale_free_background_primitive_inputs.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_h0_radius_flrw_to_scale_free_background_pipeline_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_h0_radius_flrw_to_scale_free_background_pipeline_gate.json"
)


def build_payload(
    *,
    h0_input_path: Path = H0_INPUT_PATH,
    radius_input_path: Path = RADIUS_INPUT_PATH,
    sign_input_path: Path = SIGN_INPUT_PATH,
    flrw_component_path: Path = FLRW_COMPONENT_PATH,
    omega_k_output_path: Path = OMEGA_K_OUTPUT_PATH,
    background_primitive_path: Path = BACKGROUND_PRIMITIVE_PATH,
    z_grid=None,
    z_max: float | None = None,
    z_d_bracket: list[float] | tuple[float, float] | None = None,
) -> dict:
    omega = build_omega_k_payload(
        h0_input_path=h0_input_path,
        radius_input_path=radius_input_path,
        sign_input_path=sign_input_path,
        omega_k_output_path=omega_k_output_path,
    )
    background = build_background_primitive_payload(
        flrw_component_path=flrw_component_path,
        omega_k_path=omega_k_output_path,
        background_primitive_path=background_primitive_path,
        z_grid=z_grid,
        z_max=z_max,
        z_d_bracket=z_d_bracket,
    )
    gate_passed = omega["gate_passed"] and background["gate_passed"]
    return {
        "status": "janus-z2-sigma-h0-radius-flrw-to-scale-free-background-pipeline-gate",
        "active_core": "Z2_tunnel_Sigma",
        "omega_k_pipeline_passed": omega["gate_passed"],
        "background_primitive_passed": background["gate_passed"],
        "omega_k_value": omega["omega_k_value"],
        "z_grid_length": background["z_grid_length"],
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_H0_fit": False,
        "uses_observational_curvature_fit": False,
        "gate_passed": gate_passed,
        "blocker": None
        if gate_passed
        else "missing active H0/R_curv/k inputs or active FLRW component manifest",
        "next_required": [
            "derive_active_H0_Z2Sigma_scale_convention",
            "derive_active_R_curv_Z2Sigma_and_k_branch",
            "derive_active_FLRW_components_over_rho_crit0",
            "merge_background_and_plasma_scale_free_primitives",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma H0/Radius/FLRW to Scale-Free Background Pipeline Gate",
                "",
                f"Omega_k pipeline passed: `{payload['omega_k_pipeline_passed']}`",
                f"Background primitive passed: `{payload['background_primitive_passed']}`",
                f"Gate passed: `{payload['gate_passed']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
