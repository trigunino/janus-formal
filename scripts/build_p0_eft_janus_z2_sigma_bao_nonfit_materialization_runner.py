from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_background_curvature_branch_inputs_assembler_gate import (
    build_payload as build_curvature_branch_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_curvature_radius_input_writer_gate import (
    build_payload as build_curvature_radius_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_gravity_codata_convention_gate import (
    build_payload as build_gravity_codata_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_gravity_input_writer_gate import (
    build_payload as build_gravity_input_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_scalar_inputs_assembler_gate import (
    build_payload as build_background_scalar_inputs_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_scalar_manifest_writer_from_inputs_gate import (
    build_payload as build_background_scalars_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_background_h0_input_writer_gate import (
    build_payload as build_h0_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_dimensionful_scale_separation_obligation_gate import (
    build_payload as build_dimensionful_scale_separation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_signed_cover_time_coordinate_from_projective_tunnel_gate import (
    build_payload as build_signed_time_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_signed_cover_time_parity_gate import (
    build_payload as build_time_parity_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_time_gauge_leaf_action_input_writer_gate import (
    build_payload as build_leaf_action_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projective_spatial_slice_topology_branch_gate import (
    build_payload as build_spatial_topology_branch_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_active_curvature_sign_gate import (
    build_payload as build_active_curvature_sign_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_resolved_tunnel_smooth_atlas_gate import (
    build_payload as build_resolved_tunnel_smooth_atlas_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_collar_tubular_neighborhood_gate import (
    build_payload as build_collar_tubular_neighborhood_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_resolved_tunnel_frame_bundle_gate import (
    build_payload as build_resolved_tunnel_frame_bundle_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_smooth_embedded_throat_gate import (
    build_payload as build_smooth_embedded_throat_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bao_real_state_materialization_gate import (
    build_payload as build_real_state_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_attack_order_gate import (
    build_payload as build_counterterm_attack_order_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_frontier_gate import (
    build_payload as build_matter_flux_frontier_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_radius_acyclicity_gate import (
    build_payload as build_matter_flux_radius_acyclicity_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_acyclic_route_selection_gate import (
    build_payload as build_matter_flux_acyclic_route_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_function_space_gate import (
    build_payload as build_coupled_radius_flux_function_space_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_sobolev_index_gate import (
    build_payload as build_coupled_radius_flux_sobolev_index_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_sobolev_threshold_transport_gate import (
    build_payload as build_coupled_radius_flux_sobolev_threshold_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_normal_tangent_trace_support_gate import (
    build_payload as build_coupled_radius_flux_normal_tangent_trace_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_embedding_regularity_equivariance_gate import (
    build_payload as build_embedding_regularity_equivariance_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_embedding_frame_trace_transport_gate import (
    build_payload as build_coupled_radius_flux_embedding_frame_trace_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_trace_regularity_gate import (
    build_payload as build_coupled_radius_flux_trace_regularity_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_well_posedness_gate import (
    build_payload as build_coupled_radius_flux_well_posedness_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_system_gate import (
    build_payload as build_coupled_radius_flux_system_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_gate import (
    build_payload as build_matter_flux_transparency_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_transparency_input_writer_gate import (
    build_payload as build_matter_flux_transparency_input_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_zero_component_from_transparency_gate import (
    build_payload as build_matter_flux_zero_component_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_radial_block_gate import (
    build_payload as build_matter_flux_radial_block_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_normal_matter_current_readiness_gate import (
    build_payload as build_normal_matter_current_readiness_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_reflecting_spinor_boundary_current_gate import (
    build_payload as build_reflecting_spinor_boundary_current_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spinor_projection_attack_order_gate import (
    build_payload as build_spinor_projection_attack_order_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_normal_current_gate import (
    build_payload as build_projected_dirac_normal_current_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bulk_stress_normal_flux_cancellation_gate import (
    build_payload as build_bulk_stress_normal_flux_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_radial_reduction_frontier_gate import (
    build_payload as build_counterterm_radial_reduction_frontier_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_one_form_decomposition_gate import (
    build_payload as build_counterterm_residual_one_form_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_channel_frontier_gate import (
    build_payload as build_counterterm_residual_channel_frontier_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_integrability_gate import (
    build_payload as build_counterterm_residual_integrability_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_primitive_integration_gate import (
    build_payload as build_counterterm_primitive_integration_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_extraction_gate import (
    build_payload as build_counterterm_residual_extraction_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_density_expansion_gate import (
    build_payload as build_counterterm_density_expansion_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_radial_block_gate import (
    build_payload as build_counterterm_radial_block_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_torsion_pullback_on_sigma_gate import (
    build_payload as build_torsion_pullback_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_irreducible_torsion_pullback_gate import (
    build_payload as build_flrw_irreducible_torsion_pullback_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_irreducible_torsion_components_from_pullback_gate import (
    build_payload as build_flrw_irreducible_torsion_components_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_torsion_pullback_components_from_coframe_connection_gate import (
    build_payload as build_torsion_pullback_components_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_coframe_connection_pullback_components_from_unit_q_gate import (
    build_payload as build_coframe_connection_components_from_unit_q_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_immirzi_bulk_boundary_equation_gate import (
    build_payload as build_immirzi_bulk_boundary_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_immirzi_profile_of_a_gate import (
    build_payload as build_immirzi_profile_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_holst_nieh_yan_radial_block_gate import (
    build_payload as build_holst_nieh_yan_radial_block_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_holst_nieh_yan_radial_inputs_from_torsionless_identity_gate import (
    build_payload as build_holst_nieh_yan_radial_inputs_from_torsionless_identity_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_holst_nieh_yan_radial_term_from_active_inputs_gate import (
    build_payload as build_rsigma_holst_nieh_yan_radial_term_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_grid_builder_gate import (
    build_payload as build_flrw_extrinsic_curvature_grid_builder_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_grid_writer_gate import (
    build_payload as build_flrw_extrinsic_curvature_grid_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_extrinsic_curvature_jump_builder_gate import (
    build_payload as build_extrinsic_curvature_jump_builder_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_from_extrinsic_curvature_gate import (
    build_payload as build_cartan_ghy_from_extrinsic_curvature_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_deltaK_input_writer_gate import (
    build_payload as build_cartan_ghy_deltaK_input_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_component_from_deltaK_inputs_gate import (
    build_payload as build_cartan_ghy_component_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_holst_nieh_yan_component_from_inputs_gate import (
    build_payload as build_holst_nieh_yan_component_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_component_from_inputs_gate import (
    build_payload as build_counterterm_component_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_non_matter_inputs_assembler_gate import (
    build_payload as build_flrw_non_matter_inputs_assembler_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_certificate_to_isotropic_radius_collar_gate import (
    build_payload as build_cartan_ghy_rsigma_certificate_to_isotropic_radius_collar_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_isotropic_radius_collar_input_writer_gate import (
    build_payload as build_cartan_ghy_rsigma_isotropic_radius_collar_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_gaussian_collar_input_writer_gate import (
    build_payload as build_cartan_ghy_rsigma_gaussian_collar_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_local_chart_input_writer_gate import (
    build_payload as build_cartan_ghy_rsigma_local_chart_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_chart_stencil_input_writer_gate import (
    build_payload as build_cartan_ghy_rsigma_chart_stencil_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_embedding_stencil_input_writer_gate import (
    build_payload as build_cartan_ghy_rsigma_embedding_stencil_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_radial_primitives_input_writer_gate import (
    build_payload as build_cartan_ghy_rsigma_radial_primitives_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_radial_variation_input_writer_gate import (
    build_payload as build_cartan_ghy_rsigma_radial_variation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_rsigma_radial_term_input_writer_gate import (
    build_payload as build_cartan_ghy_rsigma_radial_term_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_curvature_charge_to_saha_early_plasma_pipeline_gate import (
    build_payload as build_plasma_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_curvature_scale_flrw_to_scale_free_background_pipeline_gate import (
    build_payload as build_background_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_to_scale_free_plasma_primitive_gate import (
    build_payload as build_plasma_primitive_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_codata_constants_gate import (
    build_payload as build_plasma_codata_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_model_normalization_assembler_gate import (
    build_payload as build_plasma_model_normalization_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_baryon_photon_input_writer_gate import (
    build_payload as build_baryon_photon_input_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_ionization_thomson_input_writer_gate import (
    build_payload as build_ionization_thomson_input_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_inputs_assembler_gate import (
    build_payload as build_plasma_inputs_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_manifest_writer_from_inputs_gate import (
    build_payload as build_plasma_manifest_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_photon_temperature_firas_gate import (
    build_payload as build_photon_temperature_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_photon_density_firas_codata_gate import (
    build_payload as build_photon_density_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_photon_density_history_firas_codata_gate import (
    build_payload as build_photon_density_history_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_saha_ionization_history_gate import (
    build_payload as build_saha_history_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_saha_inputs_assembler_gate import (
    build_payload as build_saha_inputs_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_flrw_components_from_component_sources_pipeline_gate import (
    build_payload as build_flrw_components_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_physical_inputs_to_scale_free_bao_chi2_gate import (
    build_payload as build_physical_bao_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projected_baryon_noether_charge_input_gate import (
    build_payload as build_projected_charge_payload,
)
from scripts.derive_p0_eft_janus_z2_sigma_projected_charge_reduction_to_occupation import (
    build_payload as build_projected_charge_reduction_payload,
)
from scripts.write_p0_eft_janus_z2_sigma_effective_closure_from_ratio_and_occupation import (
    build_payload as build_effective_closure_from_ratio_and_occupation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spinor_bundle_projection_gate import (
    build_payload as build_spinor_bundle_projection_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_action_reduction_gate import (
    build_payload as build_projected_dirac_action_reduction_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_matter_current_gate import (
    build_payload as build_projected_dirac_matter_current_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_dirac_charge_boundary_projection_gate import (
    build_payload as build_dirac_charge_boundary_projection_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_dirac_number_normalization_gate import (
    build_payload as build_dirac_number_normalization_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_baryon_number_density_noether_volume_gate import (
    build_payload as build_baryon_density_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_certificate_from_radial_terms_gate import (
    build_payload as build_rsigma_certificate_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_isotropic_balance_solver_gate import (
    build_payload as build_rsigma_isotropic_balance_solver_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_certificate_payload_input_writer_gate import (
    build_payload as build_rsigma_certificate_payload_input_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_solver_collocation_a_grid_input_writer_gate import (
    build_payload as build_rsigma_solver_collocation_a_grid_input_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_radial_terms_input_writer_gate import (
    build_payload as build_rsigma_radial_terms_input_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_matter_flux_radial_term_from_transparency_gate import (
    build_payload as build_rsigma_matter_flux_radial_term_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_matter_flux_radial_term_from_active_projection_gate import (
    build_payload as build_rsigma_matter_flux_active_projection_radial_term_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_active_projection_radial_input_writer_gate import (
    build_payload as build_matter_flux_active_projection_radial_input_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_matter_flux_projection_components_from_embedding_stress_gate import (
    build_payload as build_matter_flux_projection_components_from_embedding_stress_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_bulk_stress_on_sigma_from_perfect_fluid_gate import (
    build_payload as build_bulk_stress_on_sigma_from_perfect_fluid_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_sector_perfect_fluid_on_sigma_input_writer_gate import (
    build_payload as build_sector_perfect_fluid_on_sigma_input_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_sector_four_velocity_from_time_direction_gate import (
    build_payload as build_sector_four_velocity_from_time_direction_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_non_cartan_rsigma_radial_terms_status_gate import (
    build_payload as build_non_cartan_rsigma_radial_terms_status_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_counterterm_radial_term_from_density_variation_gate import (
    build_payload as build_rsigma_counterterm_density_variation_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_radial_geometry_factors_from_unit_q_gate import (
    build_payload as build_counterterm_radial_geometry_factors_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_radial_density_variation_input_writer_gate import (
    build_payload as build_counterterm_radial_density_variation_input_writer_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_rsigma_solution_to_embedding_curvature_branch_gate import (
    build_payload as build_rsigma_bridge_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_active_embedding_readiness_gate import (
    build_payload as build_active_embedding_readiness_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_active_tunnel_embedding_from_radius_gate import (
    build_payload as build_active_tunnel_embedding_from_radius_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_embedding_tangent_frame_transport_gate import (
    build_payload as build_embedding_tangent_frame_transport_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_active_embedding_to_flrw_extrinsic_curvature_input_gate import (
    build_payload as build_embedding_to_flrw_extrinsic_curvature_payload,
)
from scripts.write_p0_eft_janus_z2_sigma_dynamic_shell_inputs_from_rsigma_and_bulk_f import (
    build_payload as build_dynamic_shell_inputs_from_rsigma_and_bulk_f_payload,
)
from scripts.write_p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_from_dynamic_shell import (
    build_payload as build_flrw_extrinsic_curvature_from_dynamic_shell_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_scale_free_omega_k_from_curvature_scale_gate import (
    build_payload as build_omega_k_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spatial_volume_input_writer_from_curvature_branch_gate import (
    build_payload as build_spatial_volume_input_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spatial_volume_projective_slice_gate import (
    build_payload as build_spatial_volume_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_unit_intrinsic_metric_q_ab_input_writer_gate import (
    build_payload as build_unit_intrinsic_metric_q_ab_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_nonfit_materialization_runner.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_bao_nonfit_materialization_runner.json")

Step = tuple[str, Callable[[], dict]]

DEFAULT_STEPS: tuple[Step, ...] = (
    ("scale_free_omega_k", build_omega_k_payload),
    ("signed_cover_time", build_signed_time_payload),
    ("time_parity", build_time_parity_payload),
    ("time_gauge_leaf_action", build_leaf_action_payload),
    ("spatial_topology_branch", build_spatial_topology_branch_payload),
    ("active_curvature_sign", build_active_curvature_sign_payload),
    ("background_gravity_codata", build_gravity_codata_payload),
    ("background_gravity_input", build_gravity_input_payload),
    ("resolved_tunnel_smooth_atlas", build_resolved_tunnel_smooth_atlas_payload),
    ("collar_tubular_neighborhood", build_collar_tubular_neighborhood_payload),
    ("resolved_tunnel_frame_bundle", build_resolved_tunnel_frame_bundle_payload),
    ("smooth_embedded_throat", build_smooth_embedded_throat_payload),
    ("spinor_projection_attack_order", build_spinor_projection_attack_order_payload),
    ("reflecting_spinor_boundary_current", build_reflecting_spinor_boundary_current_payload),
    ("projected_dirac_normal_current", build_projected_dirac_normal_current_payload),
    ("normal_matter_current_readiness", build_normal_matter_current_readiness_payload),
    ("bulk_stress_normal_flux", build_bulk_stress_normal_flux_payload),
    ("matter_flux_transparency", build_matter_flux_transparency_payload),
    ("matter_flux_transparency_input_writer", build_matter_flux_transparency_input_writer_payload),
    ("matter_flux_zero_component_from_transparency", build_matter_flux_zero_component_payload),
    ("matter_flux_radius_acyclicity", build_matter_flux_radius_acyclicity_payload),
    ("matter_flux_acyclic_route_selection", build_matter_flux_acyclic_route_payload),
    ("coupled_radius_flux_sobolev_index", build_coupled_radius_flux_sobolev_index_payload),
    ("coupled_radius_flux_sobolev_threshold", build_coupled_radius_flux_sobolev_threshold_payload),
    ("coupled_radius_flux_normal_tangent_trace", build_coupled_radius_flux_normal_tangent_trace_payload),
    ("embedding_regularity_equivariance", build_embedding_regularity_equivariance_payload),
    ("coupled_radius_flux_embedding_frame_trace", build_coupled_radius_flux_embedding_frame_trace_payload),
    ("coupled_radius_flux_trace_regularity", build_coupled_radius_flux_trace_regularity_payload),
    ("coupled_radius_flux_function_space", build_coupled_radius_flux_function_space_payload),
    ("coupled_radius_flux_well_posedness", build_coupled_radius_flux_well_posedness_payload),
    ("coupled_radius_flux_system", build_coupled_radius_flux_system_payload),
    ("matter_flux_frontier", build_matter_flux_frontier_payload),
    ("counterterm_residual_channel_frontier", build_counterterm_residual_channel_frontier_payload),
    ("counterterm_residual_one_form", build_counterterm_residual_one_form_payload),
    ("counterterm_residual_integrability", build_counterterm_residual_integrability_payload),
    ("counterterm_primitive_integration", build_counterterm_primitive_integration_payload),
    ("counterterm_residual_extraction", build_counterterm_residual_extraction_payload),
    ("counterterm_density_expansion", build_counterterm_density_expansion_payload),
    ("counterterm_radial_block", build_counterterm_radial_block_payload),
    ("counterterm_radial_reduction_frontier", build_counterterm_radial_reduction_frontier_payload),
    ("counterterm_attack_order", build_counterterm_attack_order_payload),
    ("matter_flux_radial_block", build_matter_flux_radial_block_payload),
    ("coframe_connection_components_from_unit_q", build_coframe_connection_components_from_unit_q_payload),
    ("torsion_pullback_components", build_torsion_pullback_components_payload),
    ("flrw_irreducible_torsion_components", build_flrw_irreducible_torsion_components_payload),
    ("flrw_irreducible_torsion_pullback", build_flrw_irreducible_torsion_pullback_payload),
    ("torsion_pullback_on_sigma", build_torsion_pullback_payload),
    ("immirzi_bulk_boundary_equation", build_immirzi_bulk_boundary_payload),
    ("immirzi_profile_of_a", build_immirzi_profile_payload),
    ("holst_nieh_yan_radial_block", build_holst_nieh_yan_radial_block_payload),
    ("rsigma_matter_flux_radial_term", build_rsigma_matter_flux_radial_term_payload),
    ("sector_four_velocity_from_time_direction", build_sector_four_velocity_from_time_direction_payload),
    ("sector_perfect_fluid_on_sigma_input_writer", build_sector_perfect_fluid_on_sigma_input_writer_payload),
    ("bulk_stress_on_sigma_from_perfect_fluid", build_bulk_stress_on_sigma_from_perfect_fluid_payload),
    ("matter_flux_projection_components_from_embedding_stress", build_matter_flux_projection_components_from_embedding_stress_payload),
    ("matter_flux_active_projection_radial_input_writer", build_matter_flux_active_projection_radial_input_writer_payload),
    ("rsigma_matter_flux_active_projection_radial_term", build_rsigma_matter_flux_active_projection_radial_term_payload),
    ("cartan_ghy_deltaK_input", build_cartan_ghy_deltaK_input_payload),
    ("cartan_ghy_component", build_cartan_ghy_component_payload),
    ("holst_nieh_yan_component", build_holst_nieh_yan_component_payload),
    ("counterterm_component", build_counterterm_component_payload),
    ("flrw_non_matter_inputs_assembler", build_flrw_non_matter_inputs_assembler_payload),
    ("rsigma_solver_collocation_a_grid_input", build_rsigma_solver_collocation_a_grid_input_payload),
    ("holst_nieh_yan_radial_inputs_from_torsionless_identity", build_holst_nieh_yan_radial_inputs_from_torsionless_identity_payload),
    ("rsigma_holst_nieh_yan_radial_term", build_rsigma_holst_nieh_yan_radial_term_payload),
    ("counterterm_radial_geometry_factors", build_counterterm_radial_geometry_factors_payload),
    ("counterterm_radial_density_variation_input_writer", build_counterterm_radial_density_variation_input_writer_payload),
    ("rsigma_counterterm_density_variation", build_rsigma_counterterm_density_variation_payload),
    ("non_cartan_rsigma_radial_terms_status", build_non_cartan_rsigma_radial_terms_status_payload),
    ("unit_intrinsic_metric_q_ab", build_unit_intrinsic_metric_q_ab_payload),
    ("rsigma_certificate_payload_input", build_rsigma_certificate_payload_input_payload),
    ("rsigma_isotropic_balance_solver", build_rsigma_isotropic_balance_solver_payload),
    ("cartan_ghy_rsigma_certificate_to_isotropic_radius_collar", build_cartan_ghy_rsigma_certificate_to_isotropic_radius_collar_payload),
    ("cartan_ghy_rsigma_isotropic_radius_collar", build_cartan_ghy_rsigma_isotropic_radius_collar_payload),
    ("cartan_ghy_rsigma_gaussian_collar", build_cartan_ghy_rsigma_gaussian_collar_payload),
    ("cartan_ghy_rsigma_local_chart", build_cartan_ghy_rsigma_local_chart_payload),
    ("cartan_ghy_rsigma_chart_stencil", build_cartan_ghy_rsigma_chart_stencil_payload),
    ("cartan_ghy_rsigma_embedding_stencil", build_cartan_ghy_rsigma_embedding_stencil_payload),
    ("cartan_ghy_rsigma_radial_primitives", build_cartan_ghy_rsigma_radial_primitives_payload),
    ("cartan_ghy_rsigma_radial_variation", build_cartan_ghy_rsigma_radial_variation_payload),
    ("cartan_ghy_rsigma_radial_term", build_cartan_ghy_rsigma_radial_term_payload),
    ("rsigma_radial_terms_input_writer", build_rsigma_radial_terms_input_payload),
    ("rsigma_certificate_from_radial_terms", build_rsigma_certificate_payload),
    ("rsigma_to_embedding_curvature_branch", build_rsigma_bridge_payload),
    ("active_embedding_readiness", build_active_embedding_readiness_payload),
    ("active_tunnel_embedding_from_radius", build_active_tunnel_embedding_from_radius_payload),
    ("embedding_tangent_frame_transport", build_embedding_tangent_frame_transport_payload),
    ("active_embedding_to_flrw_extrinsic_curvature", build_embedding_to_flrw_extrinsic_curvature_payload),
    ("dynamic_shell_inputs_from_rsigma_and_bulk_f", build_dynamic_shell_inputs_from_rsigma_and_bulk_f_payload),
    ("flrw_extrinsic_curvature_from_dynamic_shell", build_flrw_extrinsic_curvature_from_dynamic_shell_payload),
    ("flrw_extrinsic_curvature_grid_builder", build_flrw_extrinsic_curvature_grid_builder_payload),
    ("flrw_extrinsic_curvature_grid_writer", build_flrw_extrinsic_curvature_grid_writer_payload),
    ("extrinsic_curvature_jump_builder", build_extrinsic_curvature_jump_builder_payload),
    ("cartan_ghy_from_extrinsic_curvature", build_cartan_ghy_from_extrinsic_curvature_payload),
    ("background_h0", build_h0_payload),
    ("curvature_radius", build_curvature_radius_payload),
    ("dimensionful_scale_separation", build_dimensionful_scale_separation_payload),
    ("curvature_branch", build_curvature_branch_payload),
    ("background_scalar_inputs", build_background_scalar_inputs_payload),
    ("background_scalars", build_background_scalars_payload),
    ("spatial_volume_input", build_spatial_volume_input_payload),
    ("spatial_volume", build_spatial_volume_payload),
    ("spinor_bundle_projection", build_spinor_bundle_projection_payload),
    ("projected_dirac_action_reduction", build_projected_dirac_action_reduction_payload),
    ("projected_dirac_matter_current", build_projected_dirac_matter_current_payload),
    ("dirac_charge_boundary_projection", build_dirac_charge_boundary_projection_payload),
    ("dirac_number_normalization", build_dirac_number_normalization_payload),
    ("projected_charge_reduction_to_occupation", build_projected_charge_reduction_payload),
    ("projected_baryon_charge", build_projected_charge_payload),
    ("effective_closure_from_ratio_and_occupation", build_effective_closure_from_ratio_and_occupation_payload),
    ("baryon_density_noether_volume", build_baryon_density_payload),
    ("early_plasma_codata", build_plasma_codata_payload),
    ("photon_temperature_firas", build_photon_temperature_payload),
    ("photon_density_firas_codata", build_photon_density_payload),
    ("photon_density_history", build_photon_density_history_payload),
    ("early_plasma_model_normalization", build_plasma_model_normalization_payload),
    ("early_plasma_baryon_photon_input", build_baryon_photon_input_payload),
    ("early_plasma_ionization_thomson_input", build_ionization_thomson_input_payload),
    ("early_plasma_inputs", build_plasma_inputs_payload),
    ("saha_ionization_history", build_saha_history_payload),
    ("early_plasma_saha_inputs", build_saha_inputs_payload),
    ("early_plasma_manifest", build_plasma_manifest_payload),
    ("curvature_charge_saha_plasma", build_plasma_payload),
    ("flrw_components", build_flrw_components_payload),
    ("scale_free_background", build_background_payload),
    ("scale_free_plasma", build_plasma_primitive_payload),
    ("physical_bao", build_physical_bao_payload),
)


def _frontier_blocker(payload: dict) -> str | None:
    for key, value in payload.items():
        if "frontier" not in key or not isinstance(value, dict):
            continue
        blocks = value.get("blocks")
        if isinstance(blocks, list) and blocks:
            return ", ".join(str(item) for item in blocks)
        block = value.get("block")
        if block:
            return str(block)
    return None


def _missing_inputs(payload: dict) -> str | None:
    input_exists = payload.get("input_exists")
    if isinstance(input_exists, dict):
        missing = [str(key) for key, exists in input_exists.items() if exists is False]
        if missing:
            return "missing inputs: " + ", ".join(missing)
    if input_exists is False:
        return "missing input manifest"
    missing_exists = [
        key[:-7]
        for key, value in payload.items()
        if key.endswith("_exists") and value is False
    ]
    if missing_exists:
        return "missing inputs: " + ", ".join(missing_exists)
    return None


def _false_flags(payload: dict) -> str | None:
    for key in ("closure", "status_flags"):
        flags = payload.get(key)
        if isinstance(flags, dict):
            missing = [str(name) for name, value in flags.items() if value is False]
            if missing:
                return ", ".join(f"{name} = false" for name in missing)
    return None


def _step_summary(name: str, payload: dict) -> dict:
    current_frontier = payload.get("current_frontier", [])
    blocker = (
        payload.get("primary_blocker")
        or payload.get("blocker")
        or payload.get("validation_error")
        or payload.get("nearest_missing_artifact")
        or payload.get("missing_active_artifact")
        or _frontier_blocker(payload)
        or _missing_inputs(payload)
        or _false_flags(payload)
        or (
            ", ".join(str(item) for item in current_frontier)
            if isinstance(current_frontier, list) and current_frontier
            else None
        )
    )
    return {
        "name": name,
        "status": payload.get("status"),
        "gate_passed": bool(payload.get("gate_passed")),
        "blocker": blocker,
        "current_frontier": current_frontier,
        "next_required": payload.get("next_required", []),
    }


def _root_blockers(steps: list[dict]) -> list[str]:
    failed = {step["name"] for step in steps if not step["gate_passed"]}
    roots: list[str] = []
    if failed & {
        "rsigma_to_embedding_curvature_branch",
        "active_embedding_readiness",
        "active_tunnel_embedding_from_radius",
        "flrw_extrinsic_curvature_grid_writer",
        "coupled_radius_flux_system",
        "matter_flux_frontier",
        "counterterm_radial_reduction_frontier",
    }:
        roots.append("R_Sigma_solution_certificate_from_coupled_radius_flux_system")
    if failed & {
        "spinor_bundle_projection",
        "projected_dirac_action_reduction",
        "projected_dirac_matter_current",
        "dirac_charge_boundary_projection",
        "dirac_number_normalization",
        "projected_baryon_charge",
    }:
        roots.append("projected_baryon_charge_from_Dirac_projection")
    if failed & {
        "background_h0",
        "curvature_radius",
        "dimensionful_scale_separation",
        "curvature_branch",
    }:
        roots.append("active_H0_and_R_curv_dimensionful_normalization")
    if failed & {
        "early_plasma_model_normalization",
        "early_plasma_baryon_photon_input",
        "early_plasma_ionization_thomson_input",
        "early_plasma_inputs",
        "early_plasma_manifest",
        "scale_free_plasma",
    }:
        roots.append("early_plasma_manifest_from_active_baryon_photon_saha_inputs")
    if failed & {
        "cartan_ghy_component",
        "holst_nieh_yan_component",
        "counterterm_component",
        "flrw_non_matter_inputs_assembler",
        "cartan_ghy_deltaK_input",
        "flrw_components",
        "scale_free_background",
    }:
        roots.append("active_FLRW_component_manifest_from_geometric_sources")
    return roots


def _atomic_root_blockers(steps: list[dict]) -> list[str]:
    blockers: list[str] = []
    for step in steps:
        if step["gate_passed"]:
            continue
        blocker = step.get("blocker")
        if not blocker or blocker in blockers:
            continue
        blockers.append(str(blocker))
    return blockers


def _next_physical_target(atomic_root_blockers: list[str]) -> str | None:
    velocity_primitives = {
        "sector_time_direction_on_sigma_inputs",
    }
    if "sector_four_velocity_on_sigma_inputs" in atomic_root_blockers and "sector_metric_on_sigma_inputs" in atomic_root_blockers:
        return "derive_sector_metric_and_time_direction_on_Sigma_for_four_velocity"
    if velocity_primitives & set(atomic_root_blockers):
        return "derive_sector_time_direction_on_Sigma_for_four_velocity"
    sector_fluid_primitives = {
        "sector_density_pressure_on_sigma_inputs",
        "sector_metric_on_sigma_inputs",
        "sector_four_velocity_on_sigma_inputs",
    }
    if sector_fluid_primitives & set(atomic_root_blockers):
        return "derive_sector_density_pressure_metric_and_four_velocity_on_Sigma"
    if "sector_perfect_fluid_on_sigma_inputs" in atomic_root_blockers:
        return "derive_sector_rho_p_metric_and_four_velocity_on_Sigma_for_bulk_stress"
    matter_flux_projection_primitives = {
        "active_tunnel_embedding_geometry_inputs",
        "bulk_stress_on_sigma_inputs",
        "radial_variation_tangent_weights_inputs",
    }
    if (
        matter_flux_projection_primitives & set(atomic_root_blockers)
        and "counterterm_radial_density_variation_inputs" in atomic_root_blockers
    ):
        return "derive_matter_flux_projection_primitives_and_counterterm_radial_density_variation_inputs"
    if matter_flux_projection_primitives & set(atomic_root_blockers):
        return "derive_active_embedding_bulk_stress_and_radial_weights_for_matter_flux_projection"
    if {
        "active_matter_flux_projection_components",
        "counterterm_radial_density_variation_inputs",
    }.issubset(set(atomic_root_blockers)):
        return "derive_active_matter_flux_projection_components_and_counterterm_radial_density_variation_inputs"
    if "active_matter_flux_projection_components" in atomic_root_blockers:
        return "derive_active_matter_flux_projection_components_Tpm_tangents_normals_radial_weights"
    if "counterterm_radial_density_variation_inputs" in atomic_root_blockers:
        return "derive_counterterm_radial_density_variation_inputs_sqrt_h_Lct_radial_derivatives"
    if any(
        blocker in {
            "R_Sigma_radial_terms_inputs",
            "rsigma_certificate_payload_inputs",
            "R_Sigma_isotropic_balance_inputs",
        }
        for blocker in atomic_root_blockers
    ):
        return "derive_non_Cartan_RSigma_radial_terms_E_HolstNiehYan_E_matterFlux_E_counterterm"
    if any("R_Sigma_solution_certificate" in blocker for blocker in atomic_root_blockers):
        return "R_Sigma_solution_certificate"
    if atomic_root_blockers:
        return atomic_root_blockers[0]
    return None


def build_payload(
    *,
    materialization_steps: tuple[Step, ...] = DEFAULT_STEPS,
    real_state_builder: Callable[[], dict] = build_real_state_payload,
) -> dict:
    steps = []
    for name, builder in materialization_steps:
        try:
            steps.append(_step_summary(name, builder()))
        except Exception as exc:
            steps.append(
                {
                    "name": name,
                    "status": "exception",
                    "gate_passed": False,
                    "blocker": str(exc),
                }
            )

    real_state = real_state_builder()
    atomic_root_blockers = _atomic_root_blockers(steps)
    return {
        "status": "janus-z2-sigma-bao-nonfit-materialization-runner",
        "active_core": "Z2_tunnel_Sigma",
        "steps": steps,
        "root_blockers": _root_blockers(steps),
        "atomic_root_blockers": atomic_root_blockers,
        "next_physical_target": _next_physical_target(atomic_root_blockers),
        "calculator_status": (
            "ready_for_strict_inputs"
            if bool(real_state.get("pipeline_evaluable_with_strict_inputs"))
            else "not_ready"
        ),
        "steps_passed": {
            step["name"]: step["gate_passed"]
            for step in steps
        },
        "real_state_gate_passed": bool(real_state.get("gate_passed")),
        "bao_chi2_evaluated": bool(real_state.get("bao_chi2_evaluated")),
        "chi2_DESI_DR2_BAO": real_state.get("chi2_DESI_DR2_BAO"),
        "missing_real_active_inputs": real_state.get("missing_real_active_inputs", []),
        "fixture_result_is_not_physical_result": bool(
            real_state.get("fixture_result_is_not_physical_result")
        ),
        "uses_compressed_planck_lcdm": bool(real_state.get("uses_compressed_planck_lcdm")),
        "uses_archived_z4": bool(real_state.get("uses_archived_z4")),
        "uses_observational_H0_fit": bool(real_state.get("uses_observational_H0_fit")),
        "uses_observational_curvature_fit": bool(
            real_state.get("uses_observational_curvature_fit")
        ),
        "gate_passed": bool(real_state.get("gate_passed")),
        "blocker": real_state.get("blocker"),
        "next_required": real_state.get("next_required", []),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma BAO Non-Fit Materialization Runner",
        "",
        f"BAO chi2 evaluated: `{payload['bao_chi2_evaluated']}`",
        f"Real-state gate passed: `{payload['real_state_gate_passed']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Steps",
    ]
    lines.extend(
        f"- `{step['name']}`: passed=`{step['gate_passed']}`"
        + (f", blocker=`{step['blocker']}`" if step["blocker"] else "")
        for step in payload["steps"]
    )
    lines.extend(["", "## Step Frontiers"])
    for step in payload["steps"]:
        if step["current_frontier"]:
            lines.append(f"- `{step['name']}`")
            lines.extend(f"  - `{item}`" for item in step["current_frontier"])
    if payload["missing_real_active_inputs"]:
        lines.extend(["", "## Missing Real Active Inputs"])
        lines.extend(f"- `{item}`" for item in payload["missing_real_active_inputs"])
    if payload["root_blockers"]:
        lines.extend(["", "## Root Blockers"])
        lines.extend(f"- `{item}`" for item in payload["root_blockers"])
    if payload["atomic_root_blockers"]:
        lines.extend(["", "## Atomic Root Blockers"])
        lines.extend(f"- `{item}`" for item in payload["atomic_root_blockers"])
    if payload["blocker"]:
        lines.extend(["", "## Blocker", payload["blocker"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
