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
from scripts.build_p0_eft_janus_z2_sigma_scale_free_omega_k_from_curvature_scale_gate import (
    build_payload as build_omega_k_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_dimensionless_curvature_scale_from_branch_gate import (
    build_payload as build_scale_from_branch_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_components_from_component_sources_pipeline_gate import (
    build_payload as build_flrw_components_pipeline_payload,
)


SIGN_INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_sign_inputs.json")
CURVATURE_BRANCH_PATH = Path("outputs/active_z2_sigma/background_curvature_branch_inputs.json")
SCALE_NORMALIZATION_PATH = Path(
    "outputs/active_z2_sigma/background_dimensionless_curvature_scale_normalization_inputs.json"
)
SCALE_INPUT_PATH = Path("outputs/active_z2_sigma/background_dimensionless_curvature_scale_inputs.json")
FLRW_COMPONENT_PATH = Path("outputs/active_z2_sigma/flrw_components.json")
OMEGA_K_OUTPUT_PATH = Path("outputs/active_z2_sigma/background_scale_free_omega_k_inputs.json")
BACKGROUND_PRIMITIVE_PATH = Path("outputs/active_z2_sigma/bao_scale_free_background_primitive_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_curvature_scale_flrw_to_scale_free_background_pipeline_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_curvature_scale_flrw_to_scale_free_background_pipeline_gate.json"
)


def build_payload(
    *,
    sign_input_path: Path = SIGN_INPUT_PATH,
    curvature_branch_path: Path = CURVATURE_BRANCH_PATH,
    scale_normalization_path: Path = SCALE_NORMALIZATION_PATH,
    scale_input_path: Path = SCALE_INPUT_PATH,
    flrw_component_path: Path = FLRW_COMPONENT_PATH,
    omega_k_output_path: Path = OMEGA_K_OUTPUT_PATH,
    background_primitive_path: Path = BACKGROUND_PRIMITIVE_PATH,
    z_grid=None,
    z_max: float | None = None,
    z_d_bracket: list[float] | tuple[float, float] | None = None,
) -> dict:
    if flrw_component_path == FLRW_COMPONENT_PATH:
        flrw_pipeline = build_flrw_components_pipeline_payload(
            flrw_manifest_path=flrw_component_path
        )
    else:
        flrw_pipeline = {
            "status": "custom-flrw-component-manifest",
            "gate_passed": flrw_component_path.exists(),
            "upstream_frontiers": {},
            "nearest_flrw_components_frontier": {
                "blocks": [] if flrw_component_path.exists() else ["flrw_components"],
                "diagnostic_only": True,
            },
        }
    scale_from_branch = build_scale_from_branch_payload(
        input_path=curvature_branch_path,
        output_path=scale_normalization_path,
    )
    omega = build_omega_k_payload(
        sign_input_path=sign_input_path,
        scale_input_path=scale_input_path,
        output_path=omega_k_output_path,
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
    if gate_passed:
        blocker = None
    elif not omega["gate_passed"]:
        blocker = "missing active dimensionless curvature scale or curvature sign"
    elif flrw_component_path.exists():
        blocker = "background primitive validation failed"
    else:
        blocker = "missing active FLRW component manifest"
    return {
        "status": "janus-z2-sigma-curvature-scale-flrw-to-scale-free-background-pipeline-gate",
        "active_core": "Z2_tunnel_Sigma",
        "omega_k_from_curvature_scale_passed": omega["gate_passed"],
        "background_primitive_passed": background["gate_passed"],
        "flrw_component_manifest": str(flrw_component_path),
        "flrw_component_manifest_available": flrw_component_path.exists(),
        "upstream_frontiers": {
            "flrw_components": {
                "gate": flrw_pipeline["status"],
                "passed": flrw_pipeline["gate_passed"],
                "upstream_frontiers": flrw_pipeline["upstream_frontiers"],
                "nearest_frontier": flrw_pipeline["nearest_flrw_components_frontier"],
            },
            "dimensionless_curvature_scale_from_branch": {
                "gate": scale_from_branch["status"],
                "passed": scale_from_branch["gate_passed"],
                "input_exists": scale_from_branch["input_exists"],
                "curvature_branch_assembler_passed": scale_from_branch[
                    "curvature_branch_assembler_passed"
                ],
            },
        },
        "omega_k_value": omega["omega_k_value"],
        "z_grid_length": background["z_grid_length"],
        "background_validation_error": background["validation_error"],
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_H0_fit": False,
        "uses_observational_curvature_fit": False,
        "gate_passed": gate_passed,
        "blocker": blocker,
        "next_required": [
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
                "# Janus Z2/Sigma Curvature-Scale/FLRW To Scale-Free Background Pipeline Gate",
                "",
                f"Omega_k from curvature scale passed: `{payload['omega_k_from_curvature_scale_passed']}`",
                f"Background primitive passed: `{payload['background_primitive_passed']}`",
                f"Gate passed: `{payload['gate_passed']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
