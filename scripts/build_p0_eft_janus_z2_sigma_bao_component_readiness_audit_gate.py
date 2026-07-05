from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_flrw_projection_gate import (
    build_payload as build_cartan_ghy_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_scalar_manifest_gate import (
    build_payload as build_background_scalar_manifest_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_h0_input_writer_gate import (
    build_payload as build_background_h0_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_curvature_input_writer_gate import (
    build_payload as build_background_curvature_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_curvature_normalization_from_branch_gate import (
    build_payload as build_curvature_normalization_from_branch_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_curvature_branch_inputs_assembler_gate import (
    build_payload as build_curvature_branch_inputs_assembler_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_curvature_radius_input_writer_gate import (
    build_payload as build_background_curvature_radius_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_active_omega_k_derivation_gate import (
    build_payload as build_active_omega_k_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_scale_free_omega_k_from_curvature_scale_gate import (
    build_payload as build_scale_free_omega_k_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_h0_radius_to_scale_free_omega_k_pipeline_gate import (
    build_payload as build_h0_radius_to_scale_free_omega_k_pipeline_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_h0_radius_flrw_to_scale_free_background_pipeline_gate import (
    build_payload as build_h0_radius_flrw_to_scale_free_background_pipeline_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_curvature_scale_flrw_to_scale_free_background_pipeline_gate import (
    build_payload as build_curvature_scale_flrw_to_scale_free_background_pipeline_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_dimensionless_curvature_scale_from_h0_radius_gate import (
    build_payload as build_dimensionless_curvature_scale_from_h0_radius_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_dimensionless_curvature_scale_input_writer_gate import (
    build_payload as build_dimensionless_curvature_scale_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_active_curvature_sign_gate import (
    build_payload as build_active_curvature_sign_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rp3_spatial_slice_curvature_sign_gate import (
    build_payload as build_rp3_spatial_slice_curvature_sign_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rp3_spatial_slice_input_writer_from_projective_foliation_gate import (
    build_payload as build_rp3_spatial_slice_input_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projective_foliation_compatibility_gate import (
    build_payload as build_projective_foliation_compatibility_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projective_spatial_slice_topology_branch_gate import (
    build_payload as build_projective_spatial_slice_topology_branch_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_time_gauge_leaf_action_input_writer_gate import (
    build_payload as build_time_gauge_leaf_action_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_signed_cover_time_parity_gate import (
    build_payload as build_signed_cover_time_parity_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_signed_cover_time_coordinate_from_projective_tunnel_gate import (
    build_payload as build_signed_cover_time_coordinate_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_active_flrw_spatial_metric_branch_gate import (
    build_payload as build_active_flrw_spatial_metric_branch_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_gravity_input_writer_gate import (
    build_payload as build_background_gravity_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_gravity_codata_convention_gate import (
    build_payload as build_background_gravity_codata_convention_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_scalar_inputs_assembler_gate import (
    build_payload as build_background_scalar_inputs_assembler_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_scalar_manifest_writer_from_inputs_gate import (
    build_payload as build_background_scalar_writer_from_inputs_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_physical_input_obligation_gate import (
    build_payload as build_background_physical_input_obligation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_from_extrinsic_curvature_gate import (
    build_payload as build_cartan_from_k_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_deltaK_input_writer_gate import (
    build_payload as build_cartan_deltaK_input_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_component_from_deltaK_inputs_gate import (
    build_payload as build_cartan_from_deltaK_inputs_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_flrw_obligation_gate import (
    build_payload as build_counterterm_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_component_from_inputs_gate import (
    build_payload as build_counterterm_component_from_inputs_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_critical_normalization_builder_gate import (
    build_payload as build_critical_normalization_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_drag_epoch_bracket_finder_gate import (
    build_payload as build_drag_bracket_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_dirac_decoupling_condition_gate import (
    build_payload as build_dirac_decoupling_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_dirac_interaction_rate_of_a_gate import (
    build_payload as build_dirac_interaction_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_density_builder_gate import (
    build_payload as build_early_density_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_component_manifest_gate import (
    build_payload as build_early_component_manifest_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_baryon_photon_input_writer_gate import (
    build_payload as build_early_plasma_baryon_photon_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_ionization_thomson_input_writer_gate import (
    build_payload as build_early_plasma_ionization_thomson_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_manifest_writer_from_inputs_gate import (
    build_payload as build_early_plasma_writer_from_inputs_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_inputs_assembler_gate import (
    build_payload as build_early_plasma_inputs_assembler_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_physical_input_obligation_gate import (
    build_payload as build_early_plasma_physical_input_obligation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_codata_constants_gate import (
    build_payload as build_early_plasma_codata_constants_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_photon_temperature_firas_gate import (
    build_payload as build_early_plasma_photon_temperature_firas_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_photon_density_firas_codata_gate import (
    build_payload as build_early_plasma_photon_density_firas_codata_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_photon_density_history_firas_codata_gate import (
    build_payload as build_early_plasma_photon_density_history_firas_codata_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_saha_ionization_readiness_gate import (
    build_payload as build_early_plasma_saha_ionization_readiness_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_saha_ionization_history_gate import (
    build_payload as build_saha_ionization_history_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_saha_inputs_assembler_gate import (
    build_payload as build_early_plasma_saha_inputs_assembler_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_noether_volume_to_saha_early_plasma_pipeline_gate import (
    build_payload as build_noether_volume_to_saha_early_plasma_pipeline_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_curvature_charge_to_saha_early_plasma_pipeline_gate import (
    build_payload as build_curvature_charge_to_saha_early_plasma_pipeline_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_baryon_number_density_noether_volume_gate import (
    build_payload as build_baryon_number_density_noether_volume_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projected_baryon_noether_charge_input_gate import (
    build_payload as build_projected_baryon_noether_charge_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spatial_volume_input_writer_from_curvature_branch_gate import (
    build_payload as build_spatial_volume_input_writer_from_curvature_branch_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spatial_volume_projective_slice_gate import (
    build_payload as build_spatial_volume_projective_slice_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_model_normalization_assembler_gate import (
    build_payload as build_early_plasma_model_normalization_assembler_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_component_manifest_gate import (
    build_payload as build_flrw_component_manifest_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_component_manifest_writer_from_inputs_gate import (
    build_payload as build_flrw_component_writer_from_inputs_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_components_from_component_sources_pipeline_gate import (
    build_payload as build_flrw_components_from_sources_pipeline_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_inputs_merge_transparent_matter_flux_gate import (
    build_payload as build_flrw_inputs_merge_matter_flux_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_non_matter_inputs_assembler_gate import (
    build_payload as build_flrw_non_matter_assembler_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_normalization_builder_gate import (
    build_payload as build_early_normalization_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_extrinsic_curvature_jump_builder_gate import (
    build_payload as build_delta_k_jump_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_extrinsic_curvature_tensor_builder_gate import (
    build_payload as build_k_tensor_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_grid_builder_gate import (
    build_payload as build_k_grid_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_grid_writer_gate import (
    build_payload as build_k_grid_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_holst_nieh_yan_flrw_obligation_gate import (
    build_payload as build_holst_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_holst_nieh_yan_component_from_inputs_gate import (
    build_payload as build_holst_component_from_inputs_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_flrw_obligation_gate import (
    build_payload as build_matter_flux_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_component_builder_gate import (
    build_payload as build_matter_flux_component_builder_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_zero_component_from_transparency_gate import (
    build_payload as build_matter_flux_zero_component_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_input_writer_gate import (
    build_payload as build_matter_flux_transparency_input_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_metric_geometry_primitives_gate import (
    build_payload as build_metric_geometry_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_numerical_background_closure_gate import (
    build_payload as build_background_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_component_manifest_writer_gate import (
    build_payload as build_component_manifest_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_scale_free_active_manifest_pipeline_gate import (
    build_payload as build_scale_free_active_pipeline_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_scale_free_minimal_contract_gate import (
    build_payload as build_scale_free_minimal_contract_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_component_to_scale_free_split_primitives_gate import (
    build_payload as build_component_to_split_primitives_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_to_scale_free_background_primitive_gate import (
    build_payload as build_flrw_to_scale_free_background_primitive_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_scale_free_background_primitive_input_writer_gate import (
    build_payload as build_scale_free_background_primitive_input_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_to_scale_free_background_primitive_normalization_input_gate import (
    build_payload as build_flrw_to_scale_free_background_normalization_input_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_to_scale_free_plasma_primitive_gate import (
    build_payload as build_early_plasma_to_scale_free_plasma_primitive_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_scale_free_plasma_primitive_input_writer_gate import (
    build_payload as build_scale_free_plasma_primitive_input_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_to_scale_free_plasma_primitive_normalization_input_gate import (
    build_payload as build_early_plasma_to_scale_free_plasma_normalization_input_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_component_to_scale_free_primitive_chi2_gate import (
    build_payload as build_component_to_primitive_chi2_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_active_inputs_to_scale_free_primitive_chi2_gate import (
    build_payload as build_active_inputs_to_scale_free_primitive_chi2_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_physical_inputs_to_scale_free_bao_chi2_gate import (
    build_payload as build_physical_inputs_to_scale_free_bao_chi2_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_active_primitive_physical_input_obligation_gate import (
    build_payload as build_active_primitive_physical_input_obligation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_scale_free_primitive_derivation_frontier_gate import (
    build_payload as build_scale_free_primitive_derivation_frontier_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_scale_free_primitive_chi2_gate import (
    build_payload as build_scale_free_primitive_chi2_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_scale_free_primitive_inputs_assembler_gate import (
    build_payload as build_scale_free_primitive_assembler_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_split_primitives_to_scale_free_chi2_gate import (
    build_payload as build_split_primitives_to_scale_free_chi2_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_direct_primitives_to_scale_free_chi2_gate import (
    build_payload as build_direct_primitives_to_scale_free_chi2_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_thomson_drag_rate_builder_gate import (
    build_payload as build_thomson_drag_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_radius_to_embedding_conditional_closure_gate import (
    build_payload as build_radius_to_embedding_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_throat_radius_solution_frontier_gate import (
    build_payload as build_throat_radius_solution_frontier_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_component_readiness_audit_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_component_readiness_audit_gate.json")


def _blocked_fields(groups: dict[str, dict]) -> list[str]:
    blocked: list[str] = []
    for group in groups.values():
        for field, ready in group["fields"].items():
            if not ready:
                blocked.append(field)
    return blocked


DEPENDENT_BLOCKERS = {
    "cartan_ghy_rho": ["DeltaK_s_Z2Sigma_of_a", "kappa_rho_crit0_Z2Sigma"],
    "cartan_ghy_p": [
        "DeltaK_s_Z2Sigma_of_a",
        "DeltaK_tau_Z2Sigma_of_a",
        "kappa_rho_crit0_Z2Sigma",
    ],
    "holst_nieh_yan_rho": [
        "FLRW_irreducible_torsion_pullback_on_Sigma",
        "dynamic_Immirzi_Holst_Nieh_Yan_boundary_variation",
        "Holst_Nieh_Yan_FLRW_stress_reduction",
    ],
    "holst_nieh_yan_p": [
        "FLRW_irreducible_torsion_pullback_on_Sigma",
        "dynamic_Immirzi_Holst_Nieh_Yan_boundary_variation",
        "Holst_Nieh_Yan_FLRW_stress_reduction",
    ],
    "matter_flux_rho": [
        "bulk_T_munu_plus_minus_on_active_Z2Sigma_background",
        "Sigma_transparency_condition",
        "matter_flux_FLRW_reduction",
    ],
    "matter_flux_p": [
        "bulk_T_munu_plus_minus_on_active_Z2Sigma_background",
        "Sigma_transparency_condition",
        "matter_flux_FLRW_reduction",
    ],
    "counterterm_rho": [
        "explicit_Sigma_counterterm_density",
        "counterterm_metric_variation",
        "counterterm_FLRW_stress_reduction",
        "counterterm_radial_reduction",
    ],
    "counterterm_p": [
        "explicit_Sigma_counterterm_density",
        "counterterm_metric_variation",
        "counterterm_FLRW_stress_reduction",
        "counterterm_radial_reduction",
    ],
    "H0_Z2Sigma": [
        "active_background_scale_gate",
        "close_z2_sigma_effective_fluid_numeric_closure",
        "feed_active_H0_omega_k_and_rho_eff_into_existing_H_builder",
    ],
    "kappa_rho_crit0_Z2Sigma": ["H0_Z2Sigma"],
    "omega_k_Z2Sigma": [
        "active_omega_k_derivation_gate",
        "active_flrw_spatial_metric_branch_gate",
        "active_curvature_sign_gate",
        "active_FLRW_curvature_radius_or_embedding_scale",
    ],
    "rho_baryon_Z2Sigma": ["rho_baryon0_Z2Sigma", "baryon_mass_convention_Z2Sigma"],
    "rho_photon_Z2Sigma": ["Tgamma0_Z2Sigma", "radiation_constant_Z2Sigma"],
    "Gamma_drag_Z2Sigma": ["rho_baryon_Z2Sigma", "rho_photon_Z2Sigma"],
    "Gamma_drag_over_H0_Z2Sigma": ["Gamma_drag_Z2Sigma", "H0_Z2Sigma"],
    "baryon_number_density0_m3_Z2Sigma": [
        "projected_baryon_Noether_charge_Z2Sigma",
        "active_spatial_volume0_Z2Sigma",
    ],
}


def _classify_blocked_fields(blocked_fields: list[str]) -> dict[str, list[str] | dict[str, list[str]]]:
    blocked = set(blocked_fields)
    dependent = {
        field: dependencies
        for field, dependencies in DEPENDENT_BLOCKERS.items()
        if field in blocked
    }
    direct = [field for field in blocked_fields if field not in dependent]
    return {
        "direct_blocked_fields": direct,
        "dependent_blocked_fields": dependent,
    }


ROOT_OBLIGATIONS = [
    "derive_R_Sigma_of_a_from_active_throat_radius_variational_equation",
    "derive_X_plus_minus_of_a_from_R_Sigma_and_embedding_gauge",
    "derive_DeltaK_s_tau_of_a_from_active_tunnel_embedding",
    "derive_FLRW_irreducible_torsion_pullback_on_Sigma",
    "derive_dynamic_Immirzi_Holst_Nieh_Yan_boundary_variation",
    "derive_or_reject_Sigma_transparency_condition_for_matter_flux",
    "derive_explicit_Sigma_counterterm_density_and_FLRW_variation",
    "derive_active_background_scale_H0_and_G_convention",
    "derive_active_early_plasma_normalizations_and_drag_rate",
]

REMAINING_ARTIFACT_FRONTIER = [
    {
        "artifact": "outputs/active_z2_sigma/background_H0_inputs.json",
        "classification": "physical_derivation_blocker",
        "upstream": ["active_H0_Z2Sigma_scale_convention"],
    },
    {
        "artifact": "outputs/active_z2_sigma/background_curvature_inputs.json",
        "classification": "physical_derivation_blocker",
        "upstream": ["active_projective_curvature_and_tunnel_embedding"],
    },
    {
        "artifact": "outputs/active_z2_sigma/background_gravity_inputs.json",
        "classification": "physical_derivation_blocker",
        "upstream": ["active_low_energy_G_and_kappa_rho_crit0_convention"],
    },
    {
        "artifact": "outputs/active_z2_sigma/background_scalar_inputs.json",
        "classification": "plumbing_gap_after_physical_inputs",
        "upstream": [
            "background_H0_inputs.json",
            "background_curvature_inputs.json",
            "background_gravity_inputs.json",
        ],
    },
    {
        "artifact": "outputs/active_z2_sigma/flrw_extrinsic_curvature_grid_inputs.json",
        "classification": "physical_derivation_blocker",
        "upstream": ["active_R_Sigma_of_a_and_X_plus_minus_of_a"],
    },
    {
        "artifact": "outputs/active_z2_sigma/holst_nieh_yan_components.json",
        "classification": "physical_derivation_blocker",
        "upstream": ["active_FLRW_torsion_pullback_and_Holst_variation"],
    },
    {
        "artifact": "outputs/active_z2_sigma/counterterm_components.json",
        "classification": "physical_derivation_blocker",
        "upstream": ["active_Sigma_counterterm_density_and_FLRW_variation"],
    },
    {
        "artifact": "outputs/active_z2_sigma/matter_flux_transparency_inputs.json",
        "classification": "physical_derivation_blocker",
        "upstream": ["active_Sigma_transparency_or_zero_normal_flux"],
    },
    {
        "artifact": "outputs/active_z2_sigma/flrw_component_inputs.json",
        "classification": "plumbing_gap_after_physical_inputs",
        "upstream": [
            "cartan_ghy_components.json",
            "holst_nieh_yan_components.json",
            "counterterm_components.json",
            "matter_flux_components_or_zero_flux.json",
        ],
    },
    {
        "artifact": "outputs/active_z2_sigma/early_plasma_baryon_photon_inputs.json",
        "classification": "physical_derivation_blocker",
        "upstream": ["active_baryon_photon_normalizations"],
    },
    {
        "artifact": "outputs/active_z2_sigma/projected_baryon_noether_charge_inputs.json",
        "classification": "physical_derivation_blocker",
        "upstream": ["active_projected_Noether_baryon_charge_Z2Sigma"],
    },
    {
        "artifact": "outputs/active_z2_sigma/spatial_volume_normalization_inputs.json",
        "classification": "physical_derivation_blocker",
        "upstream": ["active_spatial_volume0_Z2Sigma"],
    },
    {
        "artifact": "outputs/active_z2_sigma/early_plasma_ionization_thomson_inputs.json",
        "classification": "physical_derivation_blocker",
        "upstream": ["active_ionization_free_electron_and_Thomson_drag_inputs"],
    },
    {
        "artifact": "outputs/active_z2_sigma/early_plasma_inputs.json",
        "classification": "plumbing_gap_after_physical_inputs",
        "upstream": [
            "early_plasma_baryon_photon_inputs.json",
            "early_plasma_ionization_thomson_inputs.json",
        ],
    },
    {
        "artifact": "outputs/active_z2_sigma/bao_inputs.json",
        "classification": "plumbing_gap_after_three_active_manifests",
        "upstream": [
            "background_scalars.json",
            "flrw_components.json",
            "early_plasma.json",
        ],
    },
]

PHYSICAL_DERIVATION_FRONTIER = [
    "active_H0_Z2Sigma_scale_convention",
    "active_projective_curvature_and_tunnel_embedding",
    "active_low_energy_G_and_kappa_rho_crit0_convention",
    "active_R_Sigma_of_a_and_X_plus_minus_of_a",
    "active_FLRW_torsion_pullback_and_Holst_variation",
    "active_Sigma_counterterm_density_and_FLRW_variation",
    "active_Sigma_transparency_or_zero_normal_flux",
    "active_baryon_photon_normalizations",
    "active_projected_Noether_baryon_charge_Z2Sigma",
    "active_spatial_volume0_Z2Sigma",
    "active_ionization_free_electron_and_Thomson_drag_inputs",
]

CANONICAL_FIRST_ACTIVE_ARTIFACT = {
    "artifact": "outputs/active_z2_sigma/background_scalars.json",
    "reason": (
        "feeds omega_k_Z2Sigma and active normalization into E_Z2Sigma; "
        "also unblocks kappa_rho_crit0 normalization used by Cartan-GHY components"
    ),
    "required_upstream_inputs": [
        "outputs/active_z2_sigma/background_H0_inputs.json",
        "outputs/active_z2_sigma/background_curvature_inputs.json",
        "outputs/active_z2_sigma/background_gravity_inputs.json",
    ],
    "required_policy": [
        "active-derived provenance",
        "no compressed Planck/LCDM background",
        "no archived Z4 background",
        "no observational H0 fit",
    ],
}

CANONICAL_FIRST_SCALE_FREE_ACTIVE_ARTIFACT = {
    "artifact": "outputs/active_z2_sigma/bao_scale_free_inputs.json",
    "reason": (
        "minimal DESI BAO ratio path once active dimensionless primitives "
        "E_Z2Sigma, c_s/c, Gamma_drag/H0 and omega_k_Z2Sigma are derived"
    ),
    "required_primitives": [
        "E_Z2Sigma_of_z",
        "cs_over_c_Z2Sigma_of_z",
        "Gamma_drag_over_H0_Z2Sigma_of_z",
        "omega_k_Z2Sigma",
    ],
    "required_policy": [
        "active-derived provenance",
        "no compressed Planck/LCDM r_d",
        "no archived Z4 input",
        "no observational H0 fit",
    ],
}

NORMALIZATION_POLICY = {
    "H0_Z2Sigma_role": (
        "active normalization for H_Z2Sigma and drag-epoch solving; not an "
        "observational H0 fit"
    ),
    "bao_ratio_scale_invariance": (
        "D_M/r_d, D_H/r_d and D_V/r_d are invariant under a common H scaling "
        "when H_Z2Sigma, z_d and r_d are recomputed self-consistently"
    ),
    "G_Z2Sigma_role": (
        "critical-normalization convention for upstream component reduction; "
        "not read directly by the official BAO chi2 calculator"
    ),
    "risk": (
        "H0_Z2Sigma cannot be changed independently of Gamma_drag and z_d; "
        "the cancellation applies only to the self-consistent active pipeline"
    ),
}


NEAREST_COMPONENT_FRONTIER = {
    "component": "cartan_ghy",
    "reason": (
        "closest active FLRW component path: algebraic projection and builders are "
        "ready; remaining blockers are active DeltaK_s/tau(a) and normalization inputs"
    ),
    "missing_input_paths": [
        "outputs/active_z2_sigma/flrw_extrinsic_curvature_grid_inputs.json",
        "outputs/active_z2_sigma/flrw_extrinsic_curvature_grid.json",
        "outputs/active_z2_sigma/cartan_ghy_deltaK_inputs.json",
        "outputs/active_z2_sigma/background_scalars.json",
    ],
    "physics_blockers": [
        "derive_R_Sigma_of_a_from_active_throat_radius_variational_equation",
        "derive_X_plus_minus_of_a_from_R_Sigma_and_embedding_gauge",
        "derive_DeltaK_s_tau_of_a_from_active_tunnel_embedding",
        "derive_active_background_scale_H0_and_G_convention",
    ],
    "do_not_shortcut_with": [
        "phenomenological_DeltaK_fit",
        "compressed_Planck_LCDM_background",
        "archived_Z4_background",
    ],
}


def build_payload() -> dict:
    cartan = build_cartan_ghy_payload()
    cartan_from_k = build_cartan_from_k_payload()
    cartan_from_deltaK_inputs = build_cartan_from_deltaK_inputs_payload()
    background_scalar_manifest = build_background_scalar_manifest_payload()
    background_h0_writer = build_background_h0_writer_payload()
    background_curvature_writer = build_background_curvature_writer_payload()
    curvature_branch_inputs_assembler = build_curvature_branch_inputs_assembler_payload()
    background_curvature_radius_writer = build_background_curvature_radius_writer_payload()
    curvature_normalization_from_branch = build_curvature_normalization_from_branch_payload()
    active_omega_k = build_active_omega_k_payload()
    scale_free_omega_k = build_scale_free_omega_k_payload()
    h0_radius_to_scale_free_omega_k_pipeline = (
        build_h0_radius_to_scale_free_omega_k_pipeline_payload()
    )
    h0_radius_flrw_to_scale_free_background_pipeline = (
        build_h0_radius_flrw_to_scale_free_background_pipeline_payload()
    )
    curvature_scale_flrw_to_scale_free_background_pipeline = (
        build_curvature_scale_flrw_to_scale_free_background_pipeline_payload()
    )
    dimensionless_curvature_scale_from_h0_radius = (
        build_dimensionless_curvature_scale_from_h0_radius_payload()
    )
    dimensionless_curvature_scale_writer = build_dimensionless_curvature_scale_writer_payload()
    active_curvature_sign = build_active_curvature_sign_payload()
    projective_foliation_compatibility = build_projective_foliation_compatibility_payload()
    signed_cover_time_coordinate = build_signed_cover_time_coordinate_payload()
    signed_cover_time_parity = build_signed_cover_time_parity_payload()
    time_gauge_leaf_action_writer = build_time_gauge_leaf_action_writer_payload()
    projective_spatial_slice_topology_branch = (
        build_projective_spatial_slice_topology_branch_payload()
    )
    rp3_spatial_slice_input_writer = build_rp3_spatial_slice_input_writer_payload()
    rp3_spatial_slice_curvature_sign = build_rp3_spatial_slice_curvature_sign_payload()
    active_flrw_spatial_metric_branch = build_active_flrw_spatial_metric_branch_payload()
    background_gravity_codata_convention = build_background_gravity_codata_convention_payload(
        write_output=False
    )
    background_gravity_writer = build_background_gravity_writer_payload()
    background_scalar_inputs_assembler = build_background_scalar_inputs_assembler_payload()
    background_scalar_writer_from_inputs = build_background_scalar_writer_from_inputs_payload()
    background_physical_input_obligation = build_background_physical_input_obligation_payload()
    critical_normalization = build_critical_normalization_payload()
    metric_geometry = build_metric_geometry_payload()
    k_tensor = build_k_tensor_payload()
    k_grid = build_k_grid_payload()
    k_grid_writer = build_k_grid_writer_payload()
    delta_k_jump = build_delta_k_jump_payload()
    cartan_deltaK_input_writer = build_cartan_deltaK_input_writer_payload()
    holst = build_holst_payload()
    holst_component_from_inputs = build_holst_component_from_inputs_payload()
    matter_flux = build_matter_flux_payload()
    matter_flux_component_builder = build_matter_flux_component_builder_payload()
    matter_flux_transparency_input_writer = build_matter_flux_transparency_input_writer_payload()
    matter_flux_zero_component = build_matter_flux_zero_component_payload()
    counterterm = build_counterterm_payload()
    counterterm_component_from_inputs = build_counterterm_component_from_inputs_payload()
    background = build_background_payload()
    interaction = build_dirac_interaction_payload()
    decoupling = build_dirac_decoupling_payload()
    early_density = build_early_density_payload()
    early_component_manifest = build_early_component_manifest_payload()
    early_plasma_baryon_photon_writer = build_early_plasma_baryon_photon_writer_payload()
    early_plasma_ionization_thomson_writer = (
        build_early_plasma_ionization_thomson_writer_payload()
    )
    early_plasma_inputs_assembler = build_early_plasma_inputs_assembler_payload()
    early_plasma_physical_input_obligation = (
        build_early_plasma_physical_input_obligation_payload()
    )
    early_plasma_codata_constants = build_early_plasma_codata_constants_payload(write_output=False)
    early_plasma_photon_temperature_firas = (
        build_early_plasma_photon_temperature_firas_payload(write_output=False)
    )
    early_plasma_photon_density_firas_codata = (
        build_early_plasma_photon_density_firas_codata_payload(write_output=False)
    )
    early_plasma_photon_density_history_firas_codata = (
        build_early_plasma_photon_density_history_firas_codata_payload(write_output=False)
    )
    early_plasma_saha_ionization_readiness = (
        build_early_plasma_saha_ionization_readiness_payload()
    )
    saha_ionization_history = build_saha_ionization_history_payload(write_output=False)
    early_plasma_saha_inputs_assembler = build_early_plasma_saha_inputs_assembler_payload(
        write_output=False
    )
    noether_volume_to_saha_early_plasma_pipeline = (
        build_noether_volume_to_saha_early_plasma_pipeline_payload(write_output=False)
    )
    curvature_charge_to_saha_early_plasma_pipeline = (
        build_curvature_charge_to_saha_early_plasma_pipeline_payload(write_output=False)
    )
    baryon_number_density_noether_volume = (
        build_baryon_number_density_noether_volume_payload()
    )
    projected_baryon_noether_charge = build_projected_baryon_noether_charge_payload()
    spatial_volume_input_writer_from_curvature_branch = (
        build_spatial_volume_input_writer_from_curvature_branch_payload()
    )
    spatial_volume_projective_slice = build_spatial_volume_projective_slice_payload()
    early_plasma_model_normalization_assembler = (
        build_early_plasma_model_normalization_assembler_payload()
    )
    early_plasma_writer_from_inputs = build_early_plasma_writer_from_inputs_payload()
    flrw_component_manifest = build_flrw_component_manifest_payload()
    flrw_component_writer_from_inputs = build_flrw_component_writer_from_inputs_payload()
    flrw_components_from_sources_pipeline = (
        build_flrw_components_from_sources_pipeline_payload()
    )
    flrw_inputs_merge_matter_flux = build_flrw_inputs_merge_matter_flux_payload()
    flrw_non_matter_assembler = build_flrw_non_matter_assembler_payload()
    early_normalization = build_early_normalization_payload()
    thomson_drag = build_thomson_drag_payload()
    drag_bracket = build_drag_bracket_payload()
    component_manifest_writer = build_component_manifest_writer_payload()
    scale_free_active_pipeline = build_scale_free_active_pipeline_payload()
    scale_free_minimal_contract = build_scale_free_minimal_contract_payload()
    component_to_split_primitives = build_component_to_split_primitives_payload()
    flrw_to_scale_free_background_primitive = (
        build_flrw_to_scale_free_background_primitive_payload()
    )
    flrw_to_scale_free_background_normalization_input = (
        build_flrw_to_scale_free_background_normalization_input_payload()
    )
    scale_free_background_primitive_input_writer = (
        build_scale_free_background_primitive_input_writer_payload()
    )
    early_plasma_to_scale_free_plasma_primitive = (
        build_early_plasma_to_scale_free_plasma_primitive_payload()
    )
    early_plasma_to_scale_free_plasma_normalization_input = (
        build_early_plasma_to_scale_free_plasma_normalization_input_payload()
    )
    scale_free_plasma_primitive_input_writer = (
        build_scale_free_plasma_primitive_input_writer_payload()
    )
    component_to_primitive_chi2 = build_component_to_primitive_chi2_payload()
    active_inputs_to_scale_free_primitive_chi2 = (
        build_active_inputs_to_scale_free_primitive_chi2_payload()
    )
    physical_inputs_to_scale_free_bao_chi2 = (
        build_physical_inputs_to_scale_free_bao_chi2_payload()
    )
    active_primitive_physical_input_obligation = (
        build_active_primitive_physical_input_obligation_payload()
    )
    scale_free_primitive_derivation_frontier = (
        build_scale_free_primitive_derivation_frontier_payload()
    )
    scale_free_primitive_chi2 = build_scale_free_primitive_chi2_payload()
    scale_free_primitive_assembler = build_scale_free_primitive_assembler_payload()
    split_primitives_to_scale_free_chi2 = build_split_primitives_to_scale_free_chi2_payload()
    direct_primitives_to_scale_free_chi2 = build_direct_primitives_to_scale_free_chi2_payload()

    groups = {
        "cartan_ghy": {
            "gate": "P0EFTJanusZ2SigmaCartanGHYFLRWProjectionGate",
            "fields": {
                "cartan_ghy_rho": cartan["cartan_GHY_FLRW_scale_factor_closure_ready"],
                "cartan_ghy_p": cartan["cartan_GHY_FLRW_scale_factor_closure_ready"],
            },
            "blockers": (
                k_grid_writer["next_required"]
                + cartan_deltaK_input_writer["next_required"]
                + cartan_from_deltaK_inputs["next_required"]
                + flrw_component_writer_from_inputs["next_required"]
                + cartan["next_required"]
            ),
            "builders_ready": {
                "metric_geometry_primitives_ready": metric_geometry["gate_passed"],
                "extrinsic_curvature_tensor_builder_ready": k_tensor["gate_passed"],
                "flrw_extrinsic_curvature_grid_builder_ready": k_grid["gate_passed"],
                "flrw_extrinsic_curvature_grid_writer_ready": True,
                "flrw_extrinsic_curvature_grid_writer_passed": k_grid_writer["gate_passed"],
                "extrinsic_curvature_jump_builder_ready": delta_k_jump["gate_passed"],
                "cartan_ghy_from_K_plus_minus_builder_ready": cartan_from_k["gate_passed"],
                "cartan_ghy_deltaK_input_writer_ready": True,
                "cartan_ghy_deltaK_input_writer_passed": cartan_deltaK_input_writer[
                    "gate_passed"
                ],
                "cartan_ghy_component_from_deltaK_inputs_ready": True,
                "cartan_ghy_component_from_deltaK_inputs_passed": cartan_from_deltaK_inputs[
                    "gate_passed"
                ],
                "critical_normalization_builder_ready": critical_normalization[
                    "critical_normalization_builder_ready"
                ],
                "flrw_component_manifest_writer_ready": flrw_component_manifest["writer_ready"],
                "flrw_component_manifest_writer_from_inputs_ready": True,
                "flrw_component_manifest_writer_from_inputs_passed": flrw_component_writer_from_inputs[
                    "gate_passed"
                ],
                "flrw_components_from_component_sources_pipeline_ready": True,
                "flrw_components_from_component_sources_pipeline_passed": (
                    flrw_components_from_sources_pipeline["gate_passed"]
                ),
                "flrw_inputs_merge_transparent_matter_flux_ready": True,
                "flrw_inputs_merge_transparent_matter_flux_passed": flrw_inputs_merge_matter_flux[
                    "gate_passed"
                ],
                "flrw_non_matter_inputs_assembler_ready": True,
                "flrw_non_matter_inputs_assembler_passed": flrw_non_matter_assembler[
                    "gate_passed"
                ],
                "flrw_component_manifest_merge_ready": flrw_component_manifest[
                    "merge_into_bao_component_manifest_ready"
                ],
            },
        },
        "holst_nieh_yan": {
            "gate": "P0EFTJanusZ2SigmaHolstNiehYanFLRWObligationGate",
            "fields": {
                "holst_nieh_yan_rho": holst["holst_nieh_yan_FLRW_closure_ready"],
                "holst_nieh_yan_p": holst["holst_nieh_yan_FLRW_closure_ready"],
            },
            "builders_ready": {
                "holst_nieh_yan_component_from_inputs_ready": True,
                "holst_nieh_yan_component_from_inputs_passed": holst_component_from_inputs[
                    "gate_passed"
                ],
            },
            "blockers": holst_component_from_inputs["next_required"] + holst["next_required"],
        },
        "matter_flux": {
            "gate": "P0EFTJanusZ2SigmaMatterFluxFLRWObligationGate",
            "fields": {
                "matter_flux_rho": (
                    matter_flux["matter_flux_FLRW_closure_ready"]
                    or matter_flux_zero_component["matter_flux_rho_p_values_ready"]
                ),
                "matter_flux_p": (
                    matter_flux["matter_flux_FLRW_closure_ready"]
                    or matter_flux_zero_component["matter_flux_rho_p_values_ready"]
                ),
            },
            "builders_ready": {
                "transparent_flux_component_builder_ready": matter_flux_component_builder[
                    "transparent_flux_component_builder_ready"
                ],
                "transparency_input_writer_ready": True,
                "transparency_input_writer_passed": matter_flux_transparency_input_writer[
                    "gate_passed"
                ],
                "zero_component_from_transparency_gate_ready": True,
                "zero_component_from_transparency_gate_passed": matter_flux_zero_component[
                    "gate_passed"
                ],
                "zero_component_values_ready": matter_flux_zero_component[
                    "matter_flux_rho_p_values_ready"
                ],
            },
            "blockers": (
                matter_flux_transparency_input_writer["next_required"]
                + matter_flux_zero_component["next_required"]
                + matter_flux["next_required"]
            ),
        },
        "counterterm": {
            "gate": "P0EFTJanusZ2SigmaCountertermFLRWObligationGate",
            "fields": {
                "counterterm_rho": counterterm["counterterm_FLRW_closure_ready"],
                "counterterm_p": counterterm["counterterm_FLRW_closure_ready"],
            },
            "builders_ready": {
                "counterterm_component_from_inputs_ready": True,
                "counterterm_component_from_inputs_passed": counterterm_component_from_inputs[
                    "gate_passed"
                ],
                "counterterm_component_requires_FLRW_stress_reduced": counterterm_component_from_inputs[
                    "requires_counterterm_FLRW_stress_reduced"
                ],
                "counterterm_component_requires_radial_reduction_ready": counterterm_component_from_inputs[
                    "requires_counterterm_radial_reduction_ready"
                ],
            },
            "blockers": counterterm_component_from_inputs["next_required"] + counterterm["next_required"],
        },
        "background_scalars": {
            "gate": "P0EFTJanusZ2SigmaNumericalBackgroundClosureGate",
            "fields": {
                "H0_Z2Sigma": background["numerical_H_Z2Sigma_ready"],
                "omega_k_Z2Sigma": background["numerical_background_prerequisites_ready"],
                "kappa_rho_crit0_Z2Sigma": critical_normalization[
                    "critical_normalization_values_ready"
                ],
            },
            "builders_ready": {
                "background_scalar_manifest_writer_ready": background_scalar_manifest["writer_ready"],
                "background_h0_input_writer_ready": True,
                "background_h0_input_writer_passed": background_h0_writer["gate_passed"],
                "background_curvature_input_writer_ready": True,
                "background_curvature_input_writer_passed": background_curvature_writer[
                    "gate_passed"
                ],
                "background_curvature_normalization_from_branch_ready": True,
                "background_curvature_normalization_from_branch_passed": (
                    curvature_normalization_from_branch["gate_passed"]
                ),
                "background_curvature_branch_inputs_assembler_ready": True,
                "background_curvature_branch_inputs_assembler_passed": (
                    curvature_branch_inputs_assembler["gate_passed"]
                ),
                "background_curvature_radius_input_writer_ready": True,
                "background_curvature_radius_input_writer_passed": (
                    background_curvature_radius_writer["gate_passed"]
                ),
                "active_omega_k_formula_builder_ready": active_omega_k[
                    "omega_k_formula_builder_ready"
                ],
                "active_omega_k_values_ready": active_omega_k[
                    "omega_k_Z2Sigma_values_ready"
                ],
                "scale_free_omega_k_from_curvature_scale_ready": True,
                "scale_free_omega_k_from_curvature_scale_passed": (
                    scale_free_omega_k["gate_passed"]
                ),
                "h0_radius_to_scale_free_omega_k_pipeline_ready": True,
                "h0_radius_to_scale_free_omega_k_pipeline_passed": (
                    h0_radius_to_scale_free_omega_k_pipeline["gate_passed"]
                ),
                "h0_radius_flrw_to_scale_free_background_pipeline_ready": True,
                "h0_radius_flrw_to_scale_free_background_pipeline_passed": (
                    h0_radius_flrw_to_scale_free_background_pipeline["gate_passed"]
                ),
                "curvature_scale_flrw_to_scale_free_background_pipeline_ready": True,
                "curvature_scale_flrw_to_scale_free_background_pipeline_passed": (
                    curvature_scale_flrw_to_scale_free_background_pipeline["gate_passed"]
                ),
                "dimensionless_curvature_scale_from_h0_radius_ready": True,
                "dimensionless_curvature_scale_from_h0_radius_passed": (
                    dimensionless_curvature_scale_from_h0_radius["gate_passed"]
                ),
                "dimensionless_curvature_scale_input_writer_ready": True,
                "dimensionless_curvature_scale_input_writer_passed": (
                    dimensionless_curvature_scale_writer["gate_passed"]
                ),
                "active_flrw_spatial_metric_branch_gate_passed": (
                    active_flrw_spatial_metric_branch["gate_passed"]
                ),
                "active_flrw_spatial_metric_branch_values_ready": (
                    active_flrw_spatial_metric_branch[
                        "flrw_spatial_metric_branch_values_ready"
                    ]
                ),
                "active_curvature_sign_gate_passed": active_curvature_sign[
                    "gate_passed"
                ],
                "active_curvature_sign_values_ready": active_curvature_sign[
                    "curvature_sign_values_ready"
                ],
                "projective_foliation_to_rp3_slice_rule_ready": (
                    rp3_spatial_slice_input_writer[
                        "projective_foliation_to_rp3_slice_rule_ready"
                    ]
                ),
                "projective_foliation_compatibility_gate_passed": (
                    projective_foliation_compatibility["gate_passed"]
                ),
                "single_leaf_RP3_inference_allowed": (
                    projective_foliation_compatibility[
                        "single_leaf_RP3_inference_allowed"
                    ]
                ),
                "projective_spatial_slice_topology_branch_ready": (
                    projective_spatial_slice_topology_branch[
                        "positive_curvature_sign_supported"
                    ]
                ),
                "signed_cover_time_coordinate_from_projective_tunnel_passed": (
                    signed_cover_time_coordinate["gate_passed"]
                ),
                "signed_cover_time_parity_rule_ready": (
                    signed_cover_time_parity["signed_cover_time_parity_rule_ready"]
                ),
                "signed_cover_time_parity_input_writer_passed": (
                    signed_cover_time_parity["gate_passed"]
                ),
                "time_parity_to_leaf_action_rule_ready": (
                    time_gauge_leaf_action_writer[
                        "time_parity_to_leaf_action_rule_ready"
                    ]
                ),
                "time_gauge_leaf_action_input_writer_passed": (
                    time_gauge_leaf_action_writer["gate_passed"]
                ),
                "projective_spatial_slice_topology_branch_selected": (
                    projective_spatial_slice_topology_branch[
                        "topology_branch_selected"
                    ]
                ),
                "rp3_spatial_slice_input_writer_passed": (
                    rp3_spatial_slice_input_writer["gate_passed"]
                ),
                "rp3_spatial_slice_curvature_sign_rule_ready": (
                    rp3_spatial_slice_curvature_sign[
                        "rp3_spatial_slice_to_k_plus_one_rule_ready"
                    ]
                ),
                "rp3_spatial_slice_curvature_sign_gate_passed": (
                    rp3_spatial_slice_curvature_sign["gate_passed"]
                ),
                "background_gravity_input_writer_ready": True,
                "background_gravity_input_writer_passed": background_gravity_writer[
                    "gate_passed"
                ],
                "background_gravity_codata_convention_ready": True,
                "background_gravity_codata_convention_passed": (
                    background_gravity_codata_convention["gate_passed"]
                ),
                "background_scalar_inputs_assembler_ready": True,
                "background_scalar_inputs_assembler_passed": (
                    background_scalar_inputs_assembler["gate_passed"]
                ),
                "background_scalar_manifest_writer_from_inputs_ready": True,
                "background_scalar_manifest_writer_from_inputs_passed": (
                    background_scalar_writer_from_inputs["gate_passed"]
                ),
                "background_physical_input_obligation_ready": True,
                "background_physical_input_obligation_passed": (
                    background_physical_input_obligation["gate_passed"]
                ),
                "background_missing_physical_inputs": (
                    background_physical_input_obligation["missing_physical_inputs"]
                ),
                "critical_normalization_builder_ready": critical_normalization[
                    "critical_normalization_builder_ready"
                ],
            },
            "blockers": (
                background_h0_writer["next_required"]
                + background_curvature_writer["next_required"]
                + background_curvature_radius_writer["next_required"]
                + curvature_branch_inputs_assembler["next_required"]
                + dimensionless_curvature_scale_from_h0_radius["next_required"]
                + dimensionless_curvature_scale_writer["next_required"]
                + scale_free_omega_k["next_required"]
                + (
                    []
                    if h0_radius_to_scale_free_omega_k_pipeline["blocker"] is None
                    else [h0_radius_to_scale_free_omega_k_pipeline["blocker"]]
                )
                + background_gravity_writer["next_required"]
                + background_scalar_inputs_assembler["next_required"]
                + background_scalar_writer_from_inputs["next_required"]
                + background_scalar_manifest["next_required"]
                + background["next_required"]
                + critical_normalization["next_required"]
                + projective_foliation_compatibility["next_required"]
                + signed_cover_time_coordinate["next_required"]
                + signed_cover_time_parity["next_required"]
                + time_gauge_leaf_action_writer["next_required"]
                + projective_spatial_slice_topology_branch["next_required"]
                + rp3_spatial_slice_input_writer["next_required"]
                + rp3_spatial_slice_curvature_sign["next_required"]
            ),
        },
        "early_plasma": {
            "gate": (
                "P0EFTJanusZ2SigmaEarlyPlasmaNormalizationBuilderGate + "
                "P0EFTJanusZ2SigmaEarlyPlasmaDensityBuilderGate + "
                "P0EFTJanusZ2SigmaThomsonDragRateBuilderGate"
            ),
            "fields": {
                "photon_temperature0_Z2Sigma": early_plasma_photon_temperature_firas[
                    "gate_passed"
                ],
                "rho_photon0_Z2Sigma": early_plasma_photon_density_firas_codata[
                    "gate_passed"
                ],
                "baryon_number_density0_m3_Z2Sigma": (
                    baryon_number_density_noether_volume["gate_passed"]
                ),
                "rho_photon_history_Z2Sigma": (
                    early_plasma_photon_density_history_firas_codata["gate_passed"]
                ),
                "rho_baryon_Z2Sigma": early_density["early_plasma_density_values_ready"],
                "rho_photon_Z2Sigma": early_density["early_plasma_density_values_ready"],
                "Gamma_drag_Z2Sigma": (
                    early_normalization["early_plasma_normalization_values_ready"]
                    and thomson_drag["Gamma_drag_values_ready"]
                    and decoupling["dirac_decoupling_condition_ready"]
                ),
                "Gamma_drag_over_H0_Z2Sigma": thomson_drag[
                    "Gamma_drag_over_H0_values_ready"
                ],
            },
            "builders_ready": {
                "normalization_builder_ready": early_normalization[
                    "free_electron_normalization_chain_ready"
                ],
                "density_builder_ready": early_density["free_electron_density_builder_ready"],
                "early_plasma_component_manifest_writer_ready": early_component_manifest[
                    "writer_ready"
                ],
                "early_plasma_baryon_photon_input_writer_ready": True,
                "early_plasma_baryon_photon_input_writer_passed": (
                    early_plasma_baryon_photon_writer["gate_passed"]
                ),
                "early_plasma_ionization_thomson_input_writer_ready": True,
                "early_plasma_ionization_thomson_input_writer_passed": (
                    early_plasma_ionization_thomson_writer["gate_passed"]
                ),
                "early_plasma_inputs_assembler_ready": True,
                "early_plasma_inputs_assembler_passed": early_plasma_inputs_assembler[
                    "gate_passed"
                ],
                "early_plasma_physical_input_obligation_ready": True,
                "early_plasma_physical_input_obligation_passed": (
                    early_plasma_physical_input_obligation["gate_passed"]
                ),
                "early_plasma_codata_constants_ready": True,
                "early_plasma_codata_constants_passed": early_plasma_codata_constants[
                    "gate_passed"
                ],
                "early_plasma_photon_temperature_firas_ready": True,
                "early_plasma_photon_temperature_firas_passed": (
                    early_plasma_photon_temperature_firas["gate_passed"]
                ),
                "early_plasma_photon_density_firas_codata_ready": True,
                "early_plasma_photon_density_firas_codata_passed": (
                    early_plasma_photon_density_firas_codata["gate_passed"]
                ),
                "early_plasma_photon_density_history_firas_codata_ready": True,
                "early_plasma_photon_density_history_firas_codata_passed": (
                    early_plasma_photon_density_history_firas_codata["gate_passed"]
                ),
                "early_plasma_saha_ionization_readiness_ready": True,
                "early_plasma_saha_ionization_readiness_passed": (
                    early_plasma_saha_ionization_readiness["gate_passed"]
                ),
                "saha_ionization_history_ready": True,
                "saha_ionization_history_passed": saha_ionization_history["gate_passed"],
                "early_plasma_saha_inputs_assembler_ready": True,
                "early_plasma_saha_inputs_assembler_passed": (
                    early_plasma_saha_inputs_assembler["gate_passed"]
                ),
                "noether_volume_to_saha_early_plasma_pipeline_ready": True,
                "noether_volume_to_saha_early_plasma_pipeline_passed": (
                    noether_volume_to_saha_early_plasma_pipeline["gate_passed"]
                ),
                "curvature_charge_to_saha_early_plasma_pipeline_ready": True,
                "curvature_charge_to_saha_early_plasma_pipeline_passed": (
                    curvature_charge_to_saha_early_plasma_pipeline["gate_passed"]
                ),
                "baryon_number_density_noether_volume_ready": True,
                "baryon_number_density_noether_volume_passed": (
                    baryon_number_density_noether_volume["gate_passed"]
                ),
                "active_projected_baryon_charge_valid": (
                    baryon_number_density_noether_volume[
                        "active_projected_baryon_charge_valid"
                    ]
                ),
                "projected_baryon_noether_charge_input_ready": True,
                "projected_baryon_noether_charge_input_passed": (
                    projected_baryon_noether_charge["gate_passed"]
                ),
                "active_spatial_volume_valid": (
                    baryon_number_density_noether_volume["active_spatial_volume_valid"]
                ),
                "spatial_volume_input_writer_from_curvature_branch_ready": True,
                "spatial_volume_input_writer_from_curvature_branch_passed": (
                    spatial_volume_input_writer_from_curvature_branch["gate_passed"]
                ),
                "spatial_volume_projective_slice_formula_ready": (
                    spatial_volume_projective_slice[
                        "closed_projective_RP3_volume_formula_ready"
                    ]
                ),
                "spatial_volume_projective_slice_passed": (
                    spatial_volume_projective_slice["gate_passed"]
                ),
                "early_plasma_model_normalization_assembler_ready": True,
                "early_plasma_model_normalization_assembler_passed": (
                    early_plasma_model_normalization_assembler["gate_passed"]
                ),
                "early_plasma_missing_physical_inputs": (
                    early_plasma_physical_input_obligation["missing_physical_inputs"]
                ),
                "early_plasma_manifest_writer_from_inputs_ready": True,
                "early_plasma_manifest_writer_from_inputs_passed": early_plasma_writer_from_inputs[
                    "gate_passed"
                ],
                "early_plasma_component_manifest_merge_ready": early_component_manifest[
                    "merge_into_bao_component_manifest_ready"
                ],
                "thomson_drag_builder_ready": thomson_drag["thomson_drag_rate_builder_ready"],
                "gamma_drag_over_h0_builder_ready": thomson_drag[
                    "Gamma_drag_over_H0_builder_ready"
                ],
                "scale_free_gamma_drag_over_h0_from_active_h0_ready": thomson_drag[
                    "scale_free_Gamma_drag_over_H0_from_active_H0_ready"
                ],
                "drag_epoch_bracket_finder_ready": drag_bracket["drag_epoch_bracket_finder_ready"],
            },
            "blockers": [
                item
                for item in (
                    early_plasma_baryon_photon_writer["next_required"]
                    + early_plasma_ionization_thomson_writer["next_required"]
                    + early_plasma_inputs_assembler["next_required"]
                    + projected_baryon_noether_charge["next_required"]
                    + spatial_volume_input_writer_from_curvature_branch["next_required"]
                    + spatial_volume_projective_slice["next_required"]
                    + baryon_number_density_noether_volume["next_required"]
                    + early_plasma_model_normalization_assembler["next_required"]
                    + early_plasma_writer_from_inputs["next_required"]
                    + early_component_manifest["next_required"]
                    + early_normalization["next_required"]
                    + early_density["next_required"]
                    + thomson_drag["next_required"]
                    + interaction["next_required"]
                    + decoupling["next_required"]
                )
                if not (
                    early_plasma_photon_temperature_firas["gate_passed"]
                    and item == "derive_active_photon_temperature_history_Tgamma_Z2Sigma"
                )
                and not (
                    early_plasma_photon_density_firas_codata["gate_passed"]
                    and item == "derive_active_rho_photon0_Z2Sigma"
                )
                and item != "derive_active_rho_baryon0_Z2Sigma"
            ],
        },
    }

    blocked_fields = _blocked_fields(groups)
    blocked_field_classification = _classify_blocked_fields(blocked_fields)
    internal_derivation_writable = not blocked_fields
    strict_manifest_writable = component_manifest_writer["gate_passed"]
    component_manifest_writable = internal_derivation_writable or strict_manifest_writable
    radius_to_embedding = build_radius_to_embedding_payload()
    throat_radius_frontier = build_throat_radius_solution_frontier_payload()
    radius_embedding_frontier = {
        "conditional_radius_to_embedding_ready": radius_to_embedding[
            "radius_to_embedding_conditional_ready"
        ],
        "radius_to_embedding_unconditional_ready": radius_to_embedding[
            "radius_to_embedding_unconditional_ready"
        ],
        "R_Sigma_of_a_ready": radius_to_embedding["closure"]["R_Sigma_of_a_ready"],
        "X_plus_minus_of_a_ready": radius_to_embedding["closure"][
            "X_plus_minus_of_a_ready"
        ],
        "throat_radius_solution_certificate_ready": throat_radius_frontier[
            "throat_radius_solution_certificate_ready"
        ],
        "current_frontier": throat_radius_frontier["current_frontier"],
        "blockers": [
            "matter_flux_radial_block",
            "counterterm_radial_block",
            "solve_E_RSigma_equals_zero_without_fit",
        ],
    }
    return {
        "status": "janus-z2-sigma-bao-component-readiness-audit-gate",
        "active_core": "Z2_tunnel_Sigma",
        "component_groups": groups,
        "blocked_fields": blocked_fields,
        "blocked_field_classification": blocked_field_classification,
        "direct_blocked_fields": blocked_field_classification["direct_blocked_fields"],
        "dependent_blocked_fields": blocked_field_classification["dependent_blocked_fields"],
        "strict_manifest_inputs": {
            "background_scalar_manifest": component_manifest_writer["required_manifests"][
                "background_scalar_manifest"
            ],
            "flrw_component_manifest": component_manifest_writer["required_manifests"][
                "flrw_component_manifest"
            ],
            "early_plasma_manifest": component_manifest_writer["required_manifests"][
                "early_plasma_manifest"
            ],
            "required_manifests_available": component_manifest_writer[
                "required_manifests_available"
            ],
            "official_component_manifest_written": component_manifest_writer[
                "official_component_manifest_written"
            ],
        },
        "internal_derivation_component_inputs_ready": internal_derivation_writable,
        "strict_manifest_component_inputs_ready": strict_manifest_writable,
        "component_manifest_inputs_ready": component_manifest_writable,
        "bao_component_inputs_manifest_writable": component_manifest_writable,
        "bao_active_manifest_pipeline_gate_can_pass": component_manifest_writable,
        "bao_scale_free_active_manifest_pipeline_ready": True,
        "bao_scale_free_active_manifest_pipeline_gate_passed": scale_free_active_pipeline[
            "gate_passed"
        ],
        "bao_scale_free_active_manifest_pipeline_can_pass": component_manifest_writable,
        "bao_scale_free_minimal_contract_ready": scale_free_minimal_contract[
            "scale_free_chi2_contract_ready"
        ],
        "bao_component_to_scale_free_split_primitives_ready": True,
        "bao_component_to_scale_free_split_primitives_passed": (
            component_to_split_primitives["gate_passed"]
        ),
        "flrw_to_scale_free_background_primitive_ready": True,
        "flrw_to_scale_free_background_primitive_passed": (
            flrw_to_scale_free_background_primitive["gate_passed"]
        ),
        "flrw_to_scale_free_background_primitive_normalization_input_ready": True,
        "flrw_to_scale_free_background_primitive_normalization_input_passed": (
            flrw_to_scale_free_background_normalization_input["gate_passed"]
        ),
        "scale_free_background_primitive_input_writer_ready": True,
        "scale_free_background_primitive_input_writer_passed": (
            scale_free_background_primitive_input_writer["gate_passed"]
        ),
        "early_plasma_to_scale_free_plasma_primitive_ready": True,
        "early_plasma_to_scale_free_plasma_primitive_passed": (
            early_plasma_to_scale_free_plasma_primitive["gate_passed"]
        ),
        "early_plasma_to_scale_free_plasma_primitive_normalization_input_ready": True,
        "early_plasma_to_scale_free_plasma_primitive_normalization_input_passed": (
            early_plasma_to_scale_free_plasma_normalization_input["gate_passed"]
        ),
        "scale_free_plasma_primitive_input_writer_ready": True,
        "scale_free_plasma_primitive_input_writer_passed": (
            scale_free_plasma_primitive_input_writer["gate_passed"]
        ),
        "bao_component_to_scale_free_primitive_chi2_ready": True,
        "bao_component_to_scale_free_primitive_chi2_passed": (
            component_to_primitive_chi2["gate_passed"]
        ),
        "active_inputs_to_scale_free_primitive_chi2_ready": True,
        "active_inputs_to_scale_free_primitive_chi2_passed": (
            active_inputs_to_scale_free_primitive_chi2["gate_passed"]
        ),
        "physical_inputs_to_scale_free_bao_chi2_ready": True,
        "physical_inputs_to_scale_free_bao_chi2_passed": (
            physical_inputs_to_scale_free_bao_chi2["gate_passed"]
        ),
        "bao_active_primitive_physical_input_obligation_ready": True,
        "bao_active_primitive_physical_input_obligation_passed": (
            active_primitive_physical_input_obligation["gate_passed"]
        ),
        "bao_active_primitive_physical_missing_groups": (
            active_primitive_physical_input_obligation["missing_physical_input_groups"]
        ),
        "bao_scale_free_primitive_derivation_frontier_ready": True,
        "bao_scale_free_primitive_derivation_frontier_passed": (
            scale_free_primitive_derivation_frontier["gate_passed"]
        ),
        "bao_scale_free_primitive_derivation_frontier_blocker": (
            scale_free_primitive_derivation_frontier["blocker"]
        ),
        "bao_scale_free_primitive_chi2_gate_ready": True,
        "bao_scale_free_primitive_chi2_gate_passed": scale_free_primitive_chi2[
            "gate_passed"
        ],
        "bao_scale_free_primitive_inputs_assembler_ready": True,
        "bao_scale_free_primitive_inputs_assembler_passed": (
            scale_free_primitive_assembler["gate_passed"]
        ),
        "bao_split_primitives_to_scale_free_chi2_ready": True,
        "bao_split_primitives_to_scale_free_chi2_passed": (
            split_primitives_to_scale_free_chi2["gate_passed"]
        ),
        "bao_direct_primitives_to_scale_free_chi2_ready": True,
        "bao_direct_primitives_to_scale_free_chi2_passed": (
            direct_primitives_to_scale_free_chi2["gate_passed"]
        ),
        "bao_scale_free_primitive_input_manifest_available": scale_free_primitive_chi2[
            "primitive_input_manifest_available"
        ],
        "bao_scale_free_minimal_primitives": list(
            scale_free_minimal_contract["primitive_physical_inputs"].keys()
        ),
        "bao_official_chi2_gate_can_pass": False,
        "observational_fit_forbidden": True,
        "compressed_planck_lcdm_rd_forbidden": True,
        "archived_z4_reuse_forbidden": True,
        "gate_passed": False,
        "blocker": "active-derived BAO component fields are not all available",
        "blocking_policy": (
            "dependent fields are reported separately when they are consequences of direct "
            "missing active inputs; they still block manifest writing"
        ),
        "root_obligations": ROOT_OBLIGATIONS,
        "remaining_artifact_frontier": REMAINING_ARTIFACT_FRONTIER,
        "physical_derivation_frontier": PHYSICAL_DERIVATION_FRONTIER,
        "canonical_first_active_artifact": CANONICAL_FIRST_ACTIVE_ARTIFACT,
        "canonical_first_scale_free_active_artifact": (
            CANONICAL_FIRST_SCALE_FREE_ACTIVE_ARTIFACT
        ),
        "nearest_component_frontier": NEAREST_COMPONENT_FRONTIER,
        "radius_embedding_frontier": radius_embedding_frontier,
        "normalization_policy": NORMALIZATION_POLICY,
        "frontier_policy": (
            "plumbing gaps should not be expanded into more writers until their listed "
            "physical derivation blockers are supplied"
        ),
        "next_required": [
            "close_Cartan_GHY_DeltaK_s_and_DeltaK_tau_of_a",
            "close_Holst_Nieh_Yan_FLRW_rho_p_of_a",
            "close_matter_flux_FLRW_rho_p_or_zero",
            "close_counterterm_FLRW_rho_p_of_a",
            "close_H_Z2Sigma_numerical_background",
            "close_active_early_plasma_density_and_drag_rate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Component Readiness Audit Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Component manifest inputs ready: `{payload['component_manifest_inputs_ready']}`",
        f"Component manifest writable: `{payload['bao_component_inputs_manifest_writable']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Blocked Fields",
    ]
    lines.extend(f"- `{field}`" for field in payload["blocked_fields"])
    lines.extend(["", "## Root Obligations"])
    lines.extend(f"- `{item}`" for item in payload["root_obligations"])
    lines.extend(["", "## Physical Derivation Frontier"])
    lines.extend(f"- `{item}`" for item in payload["physical_derivation_frontier"])
    lines.extend(["", "## Canonical First Active Artifact"])
    lines.append(f"- `{payload['canonical_first_active_artifact']['artifact']}`")
    lines.extend(["", "## Canonical First Scale-Free Active Artifact"])
    lines.append(
        f"- `{payload['canonical_first_scale_free_active_artifact']['artifact']}`"
    )
    lines.extend(["", "## Nearest Component Frontier"])
    frontier = payload["nearest_component_frontier"]
    lines.append(f"- component: `{frontier['component']}`")
    lines.append(f"- reason: {frontier['reason']}")
    lines.extend(f"- missing: `{item}`" for item in frontier["missing_input_paths"])
    lines.extend(["", "## Radius/Embedding Frontier"])
    radius_frontier = payload["radius_embedding_frontier"]
    lines.append(
        "- conditional radius-to-embedding ready: "
        f"`{radius_frontier['conditional_radius_to_embedding_ready']}`"
    )
    lines.append(
        "- unconditional radius-to-embedding ready: "
        f"`{radius_frontier['radius_to_embedding_unconditional_ready']}`"
    )
    lines.append(f"- `R_Sigma(a)` ready: `{radius_frontier['R_Sigma_of_a_ready']}`")
    lines.append(
        f"- `X_+/- (a)` ready: `{radius_frontier['X_plus_minus_of_a_ready']}`"
    )
    lines.extend(f"- blocker: `{item}`" for item in radius_frontier["blockers"])
    lines.extend(["", "## Normalization Policy"])
    lines.extend(
        f"- `{key}`: {value}"
        for key, value in payload["normalization_policy"].items()
    )
    lines.extend(["", "## Remaining Artifact Frontier"])
    lines.extend(
        f"- `{item['artifact']}`: `{item['classification']}`"
        for item in payload["remaining_artifact_frontier"]
    )
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
