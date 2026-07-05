from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_bao_split_primitives_to_scale_free_chi2_gate import (
    build_payload as build_split_primitives_to_chi2_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_curvature_charge_to_saha_early_plasma_pipeline_gate import (
    build_payload as build_plasma_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_to_scale_free_plasma_primitive_gate import (
    build_payload as build_plasma_primitive_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_dimensionful_scale_separation_obligation_gate import (
    build_payload as build_dimensionful_scale_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_curvature_scale_flrw_to_scale_free_background_pipeline_gate import (
    build_payload as build_background_payload,
)


H0_INPUT_PATH = Path("outputs/active_z2_sigma/background_H0_inputs.json")
RADIUS_INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_radius_inputs.json")
SIGN_INPUT_PATH = Path("outputs/active_z2_sigma/background_curvature_sign_inputs.json")
SCALE_INPUT_PATH = Path("outputs/active_z2_sigma/background_dimensionless_curvature_scale_inputs.json")
FLRW_COMPONENT_PATH = Path("outputs/active_z2_sigma/flrw_components.json")
CURVATURE_BRANCH_PATH = Path("outputs/active_z2_sigma/background_curvature_branch_inputs.json")
CHARGE_PATH = Path("outputs/active_z2_sigma/projected_baryon_noether_charge_inputs.json")
CONSTANTS_PATH = Path("outputs/active_z2_sigma/early_plasma_codata_constants_inputs.json")
TEMPERATURE_PATH = Path("outputs/active_z2_sigma/early_plasma_photon_temperature_firas_inputs.json")
OMEGA_K_OUTPUT_PATH = Path("outputs/active_z2_sigma/background_scale_free_omega_k_inputs.json")
VOLUME_INPUT_PATH = Path("outputs/active_z2_sigma/spatial_volume_projective_slice_inputs.json")
VOLUME_PATH = Path("outputs/active_z2_sigma/spatial_volume_normalization_inputs.json")
BARYON_DENSITY_PATH = Path("outputs/active_z2_sigma/early_plasma_baryon_number_density_noether_volume_inputs.json")
SAHA_HISTORY_PATH = Path("outputs/active_z2_sigma/saha_ionization_history_inputs.json")
EARLY_PLASMA_INPUTS_PATH = Path("outputs/active_z2_sigma/early_plasma_inputs.json")
EARLY_PLASMA_MANIFEST_PATH = Path("outputs/active_z2_sigma/early_plasma.json")
BACKGROUND_PRIMITIVE_PATH = Path("outputs/active_z2_sigma/bao_scale_free_background_primitive_inputs.json")
PLASMA_PRIMITIVE_PATH = Path("outputs/active_z2_sigma/bao_scale_free_plasma_primitive_inputs.json")
PRIMITIVE_INPUT_PATH = Path("outputs/active_z2_sigma/bao_scale_free_primitive_inputs.json")
SCALE_FREE_INPUT_PATH = Path("outputs/active_z2_sigma/bao_scale_free_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_physical_inputs_to_scale_free_bao_chi2_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_physical_inputs_to_scale_free_bao_chi2_gate.json"
)


def build_payload(
    *,
    h0_input_path: Path = H0_INPUT_PATH,
    radius_input_path: Path = RADIUS_INPUT_PATH,
    sign_input_path: Path = SIGN_INPUT_PATH,
    scale_input_path: Path = SCALE_INPUT_PATH,
    flrw_component_path: Path = FLRW_COMPONENT_PATH,
    curvature_branch_path: Path = CURVATURE_BRANCH_PATH,
    charge_path: Path = CHARGE_PATH,
    constants_path: Path = CONSTANTS_PATH,
    temperature_path: Path = TEMPERATURE_PATH,
    omega_k_output_path: Path = OMEGA_K_OUTPUT_PATH,
    volume_input_path: Path = VOLUME_INPUT_PATH,
    volume_path: Path = VOLUME_PATH,
    baryon_density_path: Path = BARYON_DENSITY_PATH,
    saha_history_path: Path = SAHA_HISTORY_PATH,
    early_plasma_inputs_path: Path = EARLY_PLASMA_INPUTS_PATH,
    early_plasma_manifest_path: Path = EARLY_PLASMA_MANIFEST_PATH,
    background_primitive_path: Path = BACKGROUND_PRIMITIVE_PATH,
    plasma_primitive_path: Path = PLASMA_PRIMITIVE_PATH,
    primitive_input_path: Path = PRIMITIVE_INPUT_PATH,
    scale_free_input_path: Path = SCALE_FREE_INPUT_PATH,
) -> dict:
    plasma = build_plasma_payload(
        curvature_branch_path=curvature_branch_path,
        charge_path=charge_path,
        constants_path=constants_path,
        temperature_path=temperature_path,
        volume_input_path=volume_input_path,
        volume_path=volume_path,
        baryon_density_path=baryon_density_path,
        saha_history_path=saha_history_path,
        early_plasma_inputs_path=early_plasma_inputs_path,
        early_plasma_manifest_path=early_plasma_manifest_path,
    )
    plasma_grid = None
    plasma_z_max = None
    plasma_z_d_bracket = None
    if plasma["gate_passed"]:
        early_payload = json.loads(early_plasma_manifest_path.read_text(encoding="utf-8"))
        plasma_grid = early_payload["z_grid"]
        plasma_z_max = early_payload.get("z_max")
        plasma_z_d_bracket = early_payload.get("z_d_bracket")

    background = build_background_payload(
        sign_input_path=sign_input_path,
        scale_input_path=scale_input_path,
        flrw_component_path=flrw_component_path,
        omega_k_output_path=omega_k_output_path,
        background_primitive_path=background_primitive_path,
        z_grid=plasma_grid,
        z_max=plasma_z_max,
        z_d_bracket=plasma_z_d_bracket,
    )
    plasma_primitive = build_plasma_primitive_payload(
        early_plasma_path=early_plasma_manifest_path,
        h0_path=h0_input_path,
        plasma_primitive_path=plasma_primitive_path,
    )
    dimensionful_scale = build_dimensionful_scale_payload(
        h0_path=h0_input_path,
        radius_path=radius_input_path,
    )
    prerequisites_passed = (
        background["gate_passed"]
        and plasma["gate_passed"]
        and plasma_primitive["gate_passed"]
    )
    if not prerequisites_passed:
        blockers = [
            item
            for item in [
                background["blocker"],
                plasma["blocker"],
                plasma_primitive.get("blocker"),
                plasma_primitive.get("validation_error"),
                dimensionful_scale.get("blocker"),
            ]
            if item
        ]
        physical_frontier_summary = {
            "background": [
                "active_FLRW_component_manifest",
                "active_dimensionless_curvature_scale_or_branch",
            ],
            "matter_flux": [
                "normal_matter_current_zero",
                "bulk_stress_normal_flux_zero_or_Z2_cancellation",
                "transparent_matter_flux_component",
            ],
            "curvature_volume": [
                "do_not_invert_H0_Rcurv_over_c_product",
                "active_H0_Z2Sigma_scale_normalization",
                "active_R_curv_Z2Sigma_Mpc",
                "closed_projective_spatial_branch_k_plus_one",
                "active_spatial_volume0_Z2Sigma",
            ],
            "baryon_charge": [
                "projected_Dirac_matter_current",
                "spinor_bundle_projection",
                "projected_baryon_number_charge_Z2Sigma",
            ],
            "early_plasma": [
                "baryon_number_density0_Z2Sigma_from_Noether_volume",
                "Saha_ionization_history",
                "early_plasma_manifest",
                "Gamma_drag_over_H0_Z2Sigma",
            ],
        }
        return {
            "status": "janus-z2-sigma-physical-inputs-to-scale-free-bao-chi2-gate",
            "active_core": "Z2_tunnel_Sigma",
            "background_pipeline_passed": background["gate_passed"],
            "curvature_charge_saha_plasma_pipeline_passed": plasma["gate_passed"],
            "plasma_primitive_passed": plasma_primitive["gate_passed"],
            "upstream_frontiers": {
                "background": {
                    "gate": background["status"],
                    "passed": background["gate_passed"],
                    "omega_k_from_curvature_scale_passed": background[
                        "omega_k_from_curvature_scale_passed"
                    ],
                    "background_primitive_passed": background["background_primitive_passed"],
                    "flrw_component_manifest_available": background[
                        "flrw_component_manifest_available"
                    ],
                    "upstream_frontiers": background.get("upstream_frontiers", {}),
                    "blocker": background["blocker"],
                },
                "curvature_charge_plasma": {
                    "gate": plasma["status"],
                    "passed": plasma["gate_passed"],
                    "upstream_frontiers": plasma.get("upstream_frontiers", {}),
                    "blocker": plasma["blocker"],
                },
                "plasma_primitive": {
                    "gate": plasma_primitive["status"],
                    "passed": plasma_primitive["gate_passed"],
                    "input_exists": plasma_primitive.get("input_exists", {}),
                    "upstream_frontiers": plasma_primitive.get("upstream_frontiers", {}),
                    "nearest_frontier": plasma_primitive.get(
                        "nearest_plasma_primitive_frontier", {}
                    ),
                    "validation_error": plasma_primitive.get("validation_error"),
                    "blocker": plasma_primitive.get("blocker"),
                },
                "dimensionful_scale_separation": {
                    "gate": dimensionful_scale["status"],
                    "passed": dimensionful_scale["gate_passed"],
                    "dimensionless_scale_exists": dimensionful_scale[
                        "dimensionless_scale_exists"
                    ],
                    "h0_normalization_exists": dimensionful_scale[
                        "h0_normalization_exists"
                    ],
                    "curvature_radius_exists": dimensionful_scale[
                        "curvature_radius_exists"
                    ],
                    "can_invert_product_to_H0_or_R_curv": dimensionful_scale[
                        "can_invert_product_to_H0_or_R_curv"
                    ],
                    "blocker": dimensionful_scale["blocker"],
                },
            },
            "nearest_physical_inputs_frontier": {
                "blocks": [
                    "active_FLRW_component_manifest",
                    "active_H0_Z2Sigma_and_R_curv_Z2Sigma",
                    "projected_baryon_number_charge_Z2Sigma",
                    "early_plasma_scale_free_primitive",
                ],
                "diagnostic_only": True,
            },
            "physical_frontier_summary": physical_frontier_summary,
            "split_primitives_chi2_passed": False,
            "bao_chi2_evaluated": False,
            "chi2_DESI_DR2_BAO": None,
            "uses_compressed_planck_lcdm": False,
            "uses_archived_z4": False,
            "uses_observational_H0_fit": False,
            "uses_observational_curvature_fit": False,
            "gate_passed": False,
            "blocker": "; ".join(blockers) if blockers else "physical input pipeline incomplete",
            "next_required": [
                "derive_active_dimensionless_curvature_scale_k_and_FLRW_components",
                "derive_projected_baryon_charge_and_Saha_early_plasma",
                "rerun_split_primitives_DESI_DR2_BAO_chi2",
            ],
        }

    chi2 = build_split_primitives_to_chi2_payload(
        background_primitive_path=background_primitive_path,
        plasma_primitive_path=plasma_primitive_path,
        primitive_input_path=primitive_input_path,
        scale_free_input_path=scale_free_input_path,
    )
    return {
        "status": "janus-z2-sigma-physical-inputs-to-scale-free-bao-chi2-gate",
        "active_core": "Z2_tunnel_Sigma",
        "background_pipeline_passed": True,
        "curvature_charge_saha_plasma_pipeline_passed": True,
        "plasma_primitive_passed": True,
        "split_primitives_chi2_passed": chi2["gate_passed"],
        "bao_chi2_evaluated": chi2["bao_chi2_evaluated"],
        "chi2_DESI_DR2_BAO": chi2.get("chi2_DESI_DR2_BAO"),
        "prediction_vector": chi2.get("prediction_vector"),
        "residual_vector": chi2.get("residual_vector"),
        "Gamma_drag_over_H0_Z2Sigma_available": chi2.get(
            "Gamma_drag_over_H0_Z2Sigma_available",
            False,
        ),
        "uses_compressed_planck_lcdm": False,
        "uses_archived_z4": False,
        "uses_observational_H0_fit": False,
        "uses_observational_curvature_fit": False,
        "gate_passed": chi2["gate_passed"],
        "blocker": chi2["blocker"],
        "next_required": []
        if chi2["gate_passed"]
        else ["inspect_scale_free_primitive_DESI_DR2_BAO_chi2_blocker"],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Physical Inputs To Scale-Free BAO Chi2 Gate",
        "",
        f"Background pipeline passed: `{payload['background_pipeline_passed']}`",
        f"Curvature+charge Saha plasma pipeline passed: `{payload['curvature_charge_saha_plasma_pipeline_passed']}`",
        f"Plasma primitive passed: `{payload['plasma_primitive_passed']}`",
        f"Split-primitives chi2 passed: `{payload['split_primitives_chi2_passed']}`",
        f"BAO chi2 evaluated: `{payload['bao_chi2_evaluated']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["chi2_DESI_DR2_BAO"] is not None:
        lines.append(f"DESI DR2 BAO chi2: `{payload['chi2_DESI_DR2_BAO']}`")
    if payload["blocker"]:
        lines.append(f"Blocker: `{payload['blocker']}`")
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
