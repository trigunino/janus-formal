from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_noether_volume_to_saha_early_plasma_pipeline_gate import (
    BARYON_DENSITY_PATH,
    CONSTANTS_PATH,
    EARLY_PLASMA_INPUTS_PATH,
    EARLY_PLASMA_MANIFEST_PATH,
    SAHA_HISTORY_PATH,
    TEMPERATURE_PATH,
    build_payload as build_noether_volume_to_plasma_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_curvature_branch_inputs_assembler_gate import (
    build_payload as build_curvature_branch_assembler_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projected_baryon_noether_charge_input_gate import (
    build_payload as build_projected_charge_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spatial_volume_input_writer_from_curvature_branch_gate import (
    build_payload as build_spatial_volume_input_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spatial_volume_projective_slice_gate import (
    build_payload as build_spatial_volume_payload,
)


CURVATURE_BRANCH_PATH = Path("outputs/active_z2_sigma/background_curvature_branch_inputs.json")
CHARGE_PATH = Path("outputs/active_z2_sigma/projected_baryon_noether_charge_inputs.json")
VOLUME_INPUT_PATH = Path("outputs/active_z2_sigma/spatial_volume_projective_slice_inputs.json")
VOLUME_PATH = Path("outputs/active_z2_sigma/spatial_volume_normalization_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_curvature_charge_to_saha_early_plasma_pipeline_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_curvature_charge_to_saha_early_plasma_pipeline_gate.json"
)


def build_payload(
    *,
    curvature_branch_path: Path = CURVATURE_BRANCH_PATH,
    charge_path: Path = CHARGE_PATH,
    constants_path: Path = CONSTANTS_PATH,
    temperature_path: Path = TEMPERATURE_PATH,
    volume_input_path: Path = VOLUME_INPUT_PATH,
    volume_path: Path = VOLUME_PATH,
    baryon_density_path: Path = BARYON_DENSITY_PATH,
    saha_history_path: Path = SAHA_HISTORY_PATH,
    early_plasma_inputs_path: Path = EARLY_PLASMA_INPUTS_PATH,
    early_plasma_manifest_path: Path = EARLY_PLASMA_MANIFEST_PATH,
    write_output: bool = True,
) -> dict:
    curvature_branch = build_curvature_branch_assembler_payload(output_path=curvature_branch_path)
    projected_charge = build_projected_charge_payload(output_path=charge_path)
    volume_input = build_spatial_volume_input_payload(
        input_path=curvature_branch_path,
        output_path=volume_input_path,
    )
    volume = build_spatial_volume_payload(
        input_path=volume_input_path,
        output_path=volume_path,
    )
    plasma = build_noether_volume_to_plasma_payload(
        charge_path=charge_path,
        volume_path=volume_path,
        constants_path=constants_path,
        temperature_path=temperature_path,
        baryon_density_path=baryon_density_path,
        saha_history_path=saha_history_path,
        early_plasma_inputs_path=early_plasma_inputs_path,
        early_plasma_manifest_path=early_plasma_manifest_path,
        write_output=write_output,
    )
    gate_passed = (
        volume_input["gate_passed"]
        and volume["gate_passed"]
        and plasma["gate_passed"]
    )
    return {
        "status": "janus-z2-sigma-curvature-charge-to-saha-early-plasma-pipeline-gate",
        "active_core": "Z2_tunnel_Sigma",
        "curvature_branch_manifest": str(curvature_branch_path),
        "projected_charge_manifest": str(charge_path),
        "spatial_volume_input_passed": volume_input["gate_passed"],
        "spatial_volume_passed": volume["gate_passed"],
        "noether_volume_to_saha_early_plasma_passed": plasma["gate_passed"],
        "upstream_frontiers": {
            "curvature_branch": {
                "gate": curvature_branch["status"],
                "passed": curvature_branch["gate_passed"],
                "input_exists": curvature_branch["input_exists"],
                "nearest_frontier": curvature_branch[
                    "nearest_background_curvature_branch_frontier"
                ],
            },
            "projected_baryon_charge": {
                "gate": projected_charge["status"],
                "passed": projected_charge["gate_passed"],
                "dirac_charge_boundary_projection_ready": projected_charge[
                    "dirac_charge_boundary_projection_ready"
                ],
                "upstream_frontiers": projected_charge["upstream_frontiers"],
                "nearest_frontier": projected_charge[
                    "nearest_projected_baryon_charge_frontier"
                ],
                "validation_error": projected_charge["validation_error"],
            },
            "spatial_volume_input": {
                "gate": volume_input["status"],
                "passed": volume_input["gate_passed"],
                "input_exists": volume_input["input_exists"],
                "nearest_frontier": volume_input.get(
                    "nearest_spatial_volume_input_frontier"
                ),
            },
            "baryon_density_to_plasma": {
                "gate": plasma["status"],
                "passed": plasma["gate_passed"],
                "baryon_density_passed": plasma["baryon_density_passed"],
                "saha_history_passed": plasma["saha_history_passed"],
                "saha_inputs_passed": plasma["saha_inputs_passed"],
                "early_plasma_manifest_passed": plasma["early_plasma_manifest_passed"],
                "upstream_frontiers": plasma["upstream_frontiers"],
                "nearest_frontier": plasma["nearest_noether_volume_plasma_frontier"],
            },
        },
        "nearest_curvature_charge_plasma_frontier": {
            "blocks": [
                "active_curvature_branch_manifest",
                "projected_baryon_number_charge_Z2Sigma",
            ],
            "gates": [
                "P0EFTJanusZ2SigmaBackgroundCurvatureBranchInputsAssemblerGate",
                "P0EFTJanusZ2SigmaProjectedBaryonNoetherChargeInputGate",
            ],
            "diagnostic_only": True,
        },
        "uses_compressed_planck_lcdm_background": False,
        "uses_compressed_planck_lcdm_rd": False,
        "uses_archived_z4_inputs": False,
        "uses_observational_H0_fit": False,
        "uses_observational_curvature_fit": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": gate_passed,
        "blocker": None
        if gate_passed
        else "missing active curvature branch, projected baryon charge, or downstream plasma inputs",
        "next_required": [
            "derive_active_R_curv_Z2Sigma_and_k_Z2Sigma_branch",
            "derive_projected_baryon_number_charge_Z2Sigma",
            "combine_active_Gamma_drag_Z2Sigma_with_H_Z2Sigma_for_z_d",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Curvature+Charge to Saha Early-Plasma Pipeline Gate",
                "",
                f"Volume input passed: `{payload['spatial_volume_input_passed']}`",
                f"Spatial volume passed: `{payload['spatial_volume_passed']}`",
                f"Plasma pipeline passed: `{payload['noether_volume_to_saha_early_plasma_passed']}`",
                f"Gate passed: `{payload['gate_passed']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
