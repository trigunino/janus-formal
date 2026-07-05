import unittest

from scripts.build_p0_eft_janus_z2_sigma_bao_nonfit_materialization_runner import (
    build_payload,
)


class P0EFTJanusZ2SigmaBAONonFitMaterializationRunnerTests(unittest.TestCase):
    def test_runner_preserves_real_state_blocker(self):
        payload = build_payload(
            materialization_steps=(
                ("omega", lambda: {"status": "omega", "gate_passed": True}),
                ("h0", lambda: {"status": "h0", "gate_passed": False, "blocker": "missing H0"}),
            ),
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_H0_Z2Sigma_and_R_curv_Z2Sigma"],
                "fixture_result_is_not_physical_result": True,
                "uses_compressed_planck_lcdm": False,
                "uses_archived_z4": False,
                "uses_observational_H0_fit": False,
                "uses_observational_curvature_fit": False,
                "blocker": "real inputs incomplete",
                "next_required": ["derive_active_H0_Z2Sigma_and_R_curv_Z2Sigma_separately"],
            },
        )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["bao_chi2_evaluated"])
        self.assertTrue(payload["steps_passed"]["omega"])
        self.assertFalse(payload["steps_passed"]["h0"])
        self.assertIn("active_H0_Z2Sigma_and_R_curv_Z2Sigma", payload["missing_real_active_inputs"])
        self.assertFalse(payload["uses_compressed_planck_lcdm"])
        self.assertFalse(payload["uses_archived_z4"])

    def test_runner_can_pass_only_when_real_state_passes(self):
        payload = build_payload(
            materialization_steps=(("all", lambda: {"status": "all", "gate_passed": True}),),
            real_state_builder=lambda: {
                "gate_passed": True,
                "bao_chi2_evaluated": True,
                "chi2_DESI_DR2_BAO": 1.25,
                "missing_real_active_inputs": [],
                "fixture_result_is_not_physical_result": False,
                "uses_compressed_planck_lcdm": False,
                "uses_archived_z4": False,
                "uses_observational_H0_fit": False,
                "uses_observational_curvature_fit": False,
                "blocker": None,
                "next_required": [],
            },
        )

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["bao_chi2_evaluated"])
        self.assertEqual(payload["chi2_DESI_DR2_BAO"], 1.25)

    def test_step_summary_uses_nearest_missing_artifact(self):
        payload = build_payload(
            materialization_steps=(
                (
                    "h0",
                    lambda: {
                        "status": "h0",
                        "gate_passed": False,
                        "nearest_missing_artifact": "outputs/active_z2_sigma/background_H0_normalization_inputs.json",
                    },
                ),
            ),
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_H0_Z2Sigma_and_R_curv_Z2Sigma"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertIn("background_H0_normalization_inputs.json", payload["steps"][0]["blocker"])

    def test_step_summary_uses_primary_blocker(self):
        payload = build_payload(
            materialization_steps=(
                (
                    "counterterm",
                    lambda: {
                        "status": "counterterm",
                        "gate_passed": False,
                        "primary_blocker": "R_Sigma_solution_certificate",
                    },
                ),
            ),
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_H0_Z2Sigma_and_R_curv_Z2Sigma"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertEqual(payload["steps"][0]["blocker"], "R_Sigma_solution_certificate")

    def test_step_summary_prefers_primary_blocker_over_verbose_blocker(self):
        payload = build_payload(
            materialization_steps=(
                (
                    "flrw",
                    lambda: {
                        "status": "flrw",
                        "gate_passed": False,
                        "primary_blocker": "flrw_component_source_manifests",
                        "blocker": "missing Cartan-GHY, Holst/Nieh-Yan, or counterterm components",
                    },
                ),
            ),
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_FLRW_component_manifest"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertEqual(payload["steps"][0]["blocker"], "flrw_component_source_manifests")

    def test_next_target_prioritizes_non_cartan_rsigma_radial_terms(self):
        payload = build_payload(
            materialization_steps=(
                (
                    "rsigma_radial_terms",
                    lambda: {
                        "status": "rsigma_radial_terms",
                        "gate_passed": False,
                        "primary_blocker": "R_Sigma_radial_terms_inputs",
                    },
                ),
            ),
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["R_Sigma_solution_certificate"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertEqual(
            payload["next_physical_target"],
            "derive_non_Cartan_RSigma_radial_terms_E_HolstNiehYan_E_matterFlux_E_counterterm",
        )

    def test_step_summary_uses_frontier_blocks(self):
        payload = build_payload(
            materialization_steps=(
                (
                    "branch",
                    lambda: {
                        "status": "branch",
                        "gate_passed": False,
                        "nearest_background_curvature_branch_frontier": {
                            "blocks": ["active_H0_Z2Sigma_scale_normalization"]
                        },
                    },
                ),
            ),
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_H0_Z2Sigma_and_R_curv_Z2Sigma"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertEqual(payload["steps"][0]["blocker"], "active_H0_Z2Sigma_scale_normalization")

    def test_step_summary_uses_missing_input_exists(self):
        payload = build_payload(
            materialization_steps=(
                (
                    "volume",
                    lambda: {
                        "status": "volume",
                        "gate_passed": False,
                        "input_exists": False,
                    },
                ),
            ),
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_spatial_volume0_Z2Sigma"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertEqual(payload["steps"][0]["blocker"], "missing input manifest")

    def test_step_summary_uses_false_exists_fields(self):
        payload = build_payload(
            materialization_steps=(
                (
                    "plasma",
                    lambda: {
                        "status": "plasma",
                        "gate_passed": False,
                        "model_input_manifest_exists": False,
                    },
                ),
            ),
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["early_plasma_manifest"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertEqual(payload["steps"][0]["blocker"], "missing inputs: model_input_manifest")

    def test_step_summary_uses_false_closure_flags(self):
        payload = build_payload(
            materialization_steps=(
                (
                    "spinor",
                    lambda: {
                        "status": "spinor",
                        "gate_passed": False,
                        "closure": {
                            "plus_spinor_bundle_ready": False,
                            "Z2_normal_orientation_ready": True,
                        },
                    },
                ),
            ),
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["projected_baryon_charge"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertEqual(payload["steps"][0]["blocker"], "plus_spinor_bundle_ready = false")

    def test_default_steps_include_rsigma_bridge_before_h0(self):
        payload = build_payload(
            materialization_steps=(
                ("scale_free_omega_k", lambda: {"status": "omega", "gate_passed": True}),
                ("rsigma_to_embedding_curvature_branch", lambda: {"status": "rsigma", "gate_passed": False}),
                ("background_h0", lambda: {"status": "h0", "gate_passed": False}),
            ),
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_H0_Z2Sigma_and_R_curv_Z2Sigma"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertEqual(
            list(payload["steps_passed"])[:3],
            ["scale_free_omega_k", "rsigma_to_embedding_curvature_branch", "background_h0"],
        )

    def test_default_steps_include_embedding_bridge_frontiers(self):
        payload = build_payload(
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_tunnel_embedding_geometry"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertIn("active_embedding_readiness", payload["steps_passed"])
        self.assertIn("active_tunnel_embedding_from_radius", payload["steps_passed"])
        self.assertIn("embedding_tangent_frame_transport", payload["steps_passed"])
        self.assertIn("active_embedding_to_flrw_extrinsic_curvature", payload["steps_passed"])
        self.assertIn("flrw_extrinsic_curvature_grid_builder", payload["steps_passed"])
        self.assertIn("flrw_extrinsic_curvature_grid_writer", payload["steps_passed"])
        self.assertIn("extrinsic_curvature_jump_builder", payload["steps_passed"])
        self.assertIn("cartan_ghy_from_extrinsic_curvature", payload["steps_passed"])

    def test_step_summary_preserves_current_frontier(self):
        payload = build_payload(
            materialization_steps=(
                (
                    "rsigma",
                    lambda: {
                        "status": "rsigma",
                        "gate_passed": False,
                        "current_frontier": ["matter_flux_block_reduced = false"],
                    },
                ),
            ),
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_H0_Z2Sigma_and_R_curv_Z2Sigma"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertEqual(payload["steps"][0]["current_frontier"], ["matter_flux_block_reduced = false"])
        self.assertEqual(payload["steps"][0]["blocker"], "matter_flux_block_reduced = false")

    def test_default_steps_include_flrw_and_baryon_density_frontiers(self):
        payload = build_payload(
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_FLRW_component_manifest"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertIn("flrw_components", payload["steps_passed"])
        self.assertIn("baryon_density_noether_volume", payload["steps_passed"])

    def test_default_steps_include_projected_baryon_dirac_chain(self):
        payload = build_payload(
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["projected_baryon_charge"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertIn("spinor_bundle_projection", payload["steps_passed"])
        self.assertIn("projected_dirac_action_reduction", payload["steps_passed"])
        self.assertIn("projected_dirac_matter_current", payload["steps_passed"])
        self.assertIn("dirac_charge_boundary_projection", payload["steps_passed"])
        self.assertIn("dirac_number_normalization", payload["steps_passed"])
        self.assertIn("projected_baryon_charge", payload["steps_passed"])

    def test_default_steps_include_codata_gravity_materialization(self):
        payload = build_payload(
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_H0_Z2Sigma_and_R_curv_Z2Sigma"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertIn("background_gravity_codata", payload["steps_passed"])
        self.assertIn("background_gravity_input", payload["steps_passed"])
        self.assertIn("background_scalar_inputs", payload["steps_passed"])
        self.assertIn("background_scalars", payload["steps_passed"])

    def test_default_steps_include_direct_photon_materialization(self):
        payload = build_payload(
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["early_plasma_scale_free_primitive"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertIn("early_plasma_codata", payload["steps_passed"])
        self.assertIn("photon_temperature_firas", payload["steps_passed"])
        self.assertIn("photon_density_firas_codata", payload["steps_passed"])
        self.assertIn("photon_density_history", payload["steps_passed"])

    def test_default_steps_include_early_plasma_materialization_chain(self):
        payload = build_payload(
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["early_plasma_manifest"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertIn("early_plasma_model_normalization", payload["steps_passed"])
        self.assertIn("early_plasma_baryon_photon_input", payload["steps_passed"])
        self.assertIn("early_plasma_ionization_thomson_input", payload["steps_passed"])
        self.assertIn("early_plasma_inputs", payload["steps_passed"])
        self.assertIn("saha_ionization_history", payload["steps_passed"])
        self.assertIn("early_plasma_saha_inputs", payload["steps_passed"])
        self.assertIn("early_plasma_manifest", payload["steps_passed"])

    def test_default_steps_include_projective_curvature_sign_materialization(self):
        payload = build_payload(
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_H0_Z2Sigma_and_R_curv_Z2Sigma"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertIn("signed_cover_time", payload["steps_passed"])
        self.assertIn("time_parity", payload["steps_passed"])
        self.assertIn("time_gauge_leaf_action", payload["steps_passed"])
        self.assertIn("spatial_topology_branch", payload["steps_passed"])
        self.assertIn("active_curvature_sign", payload["steps_passed"])

    def test_default_steps_include_resolved_tunnel_geometry_frontiers(self):
        payload = build_payload(
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_embedding_geometry"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertIn("resolved_tunnel_smooth_atlas", payload["steps_passed"])
        self.assertIn("collar_tubular_neighborhood", payload["steps_passed"])
        self.assertIn("resolved_tunnel_frame_bundle", payload["steps_passed"])
        self.assertIn("smooth_embedded_throat", payload["steps_passed"])

    def test_default_steps_include_dimensionful_scale_separation(self):
        payload = build_payload(
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_H0_Z2Sigma_and_R_curv_Z2Sigma"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertIn("dimensionful_scale_separation", payload["steps_passed"])

    def test_default_steps_include_rsigma_upstream_radial_frontiers(self):
        payload = build_payload(
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_RSigma_solution_certificate"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertIn("matter_flux_frontier", payload["steps_passed"])
        self.assertIn("counterterm_radial_reduction_frontier", payload["steps_passed"])

    def test_default_steps_include_radial_subfrontiers(self):
        payload = build_payload(
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_RSigma_solution_certificate"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertIn("normal_matter_current_readiness", payload["steps_passed"])
        self.assertIn("spinor_projection_attack_order", payload["steps_passed"])
        self.assertIn("reflecting_spinor_boundary_current", payload["steps_passed"])
        self.assertIn("projected_dirac_normal_current", payload["steps_passed"])
        self.assertIn("bulk_stress_normal_flux", payload["steps_passed"])
        self.assertIn("matter_flux_transparency", payload["steps_passed"])
        self.assertIn("matter_flux_transparency_input_writer", payload["steps_passed"])
        self.assertIn("matter_flux_zero_component_from_transparency", payload["steps_passed"])
        self.assertIn("matter_flux_radius_acyclicity", payload["steps_passed"])
        self.assertIn("matter_flux_acyclic_route_selection", payload["steps_passed"])
        self.assertIn("coupled_radius_flux_sobolev_index", payload["steps_passed"])
        self.assertIn("coupled_radius_flux_sobolev_threshold", payload["steps_passed"])
        self.assertIn("coupled_radius_flux_normal_tangent_trace", payload["steps_passed"])
        self.assertIn("embedding_regularity_equivariance", payload["steps_passed"])
        self.assertIn("coupled_radius_flux_embedding_frame_trace", payload["steps_passed"])
        self.assertIn("coupled_radius_flux_trace_regularity", payload["steps_passed"])
        self.assertIn("coupled_radius_flux_function_space", payload["steps_passed"])
        self.assertIn("coupled_radius_flux_well_posedness", payload["steps_passed"])
        self.assertIn("coupled_radius_flux_system", payload["steps_passed"])
        self.assertIn("counterterm_residual_channel_frontier", payload["steps_passed"])
        self.assertIn("matter_flux_radial_block", payload["steps_passed"])
        self.assertIn("coframe_connection_components_from_unit_q", payload["steps_passed"])
        self.assertIn("torsion_pullback_components", payload["steps_passed"])
        self.assertIn("torsion_pullback_on_sigma", payload["steps_passed"])
        self.assertIn("flrw_irreducible_torsion_components", payload["steps_passed"])
        self.assertIn("immirzi_bulk_boundary_equation", payload["steps_passed"])
        self.assertIn("immirzi_profile_of_a", payload["steps_passed"])
        self.assertIn("holst_nieh_yan_radial_block", payload["steps_passed"])
        self.assertIn("holst_nieh_yan_radial_inputs_from_torsionless_identity", payload["steps_passed"])
        self.assertIn("rsigma_holst_nieh_yan_radial_term", payload["steps_passed"])
        self.assertIn("rsigma_matter_flux_radial_term", payload["steps_passed"])
        self.assertIn("rsigma_matter_flux_active_projection_radial_term", payload["steps_passed"])
        self.assertIn("counterterm_residual_one_form", payload["steps_passed"])
        self.assertIn("counterterm_residual_integrability", payload["steps_passed"])
        self.assertIn("counterterm_primitive_integration", payload["steps_passed"])
        self.assertIn("counterterm_residual_extraction", payload["steps_passed"])
        self.assertIn("counterterm_density_expansion", payload["steps_passed"])
        self.assertIn("counterterm_radial_block", payload["steps_passed"])
        self.assertIn("flrw_irreducible_torsion_pullback", payload["steps_passed"])
        self.assertIn("non_cartan_rsigma_radial_terms_status", payload["steps_passed"])
        self.assertIn("cartan_ghy_deltaK_input", payload["steps_passed"])
        self.assertIn("cartan_ghy_component", payload["steps_passed"])
        self.assertIn("holst_nieh_yan_component", payload["steps_passed"])
        self.assertIn("counterterm_component", payload["steps_passed"])
        self.assertIn("flrw_non_matter_inputs_assembler", payload["steps_passed"])
        self.assertIn("rsigma_solver_collocation_a_grid_input", payload["steps_passed"])

    def test_runner_reports_root_blockers(self):
        payload = build_payload(
            materialization_steps=(
                ("rsigma_to_embedding_curvature_branch", lambda: {"status": "rsigma", "gate_passed": False, "primary_blocker": "R_Sigma_solution_certificate"}),
                ("projected_baryon_charge", lambda: {"status": "charge", "gate_passed": False, "primary_blocker": "R_Sigma_solution_certificate"}),
                ("background_h0", lambda: {"status": "h0", "gate_passed": False, "primary_blocker": "active_H0_Z2Sigma_scale_normalization"}),
                ("early_plasma_manifest", lambda: {"status": "plasma", "gate_passed": False, "primary_blocker": "early_plasma_manifest"}),
                ("flrw_components", lambda: {"status": "flrw", "gate_passed": False, "primary_blocker": "flrw_component_source_manifests"}),
            ),
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_FLRW_component_manifest"],
                "fixture_result_is_not_physical_result": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertEqual(
            payload["root_blockers"],
            [
                "R_Sigma_solution_certificate_from_coupled_radius_flux_system",
                "projected_baryon_charge_from_Dirac_projection",
                "active_H0_and_R_curv_dimensionful_normalization",
                "early_plasma_manifest_from_active_baryon_photon_saha_inputs",
                "active_FLRW_component_manifest_from_geometric_sources",
            ],
        )
        self.assertEqual(
            payload["atomic_root_blockers"],
            [
                "R_Sigma_solution_certificate",
                "active_H0_Z2Sigma_scale_normalization",
                "early_plasma_manifest",
                "flrw_component_source_manifests",
            ],
        )
        self.assertEqual(payload["next_physical_target"], "R_Sigma_solution_certificate")

    def test_runner_reports_calculator_status_separately_from_physics_blocker(self):
        payload = build_payload(
            materialization_steps=(
                (
                    "rsigma_to_embedding_curvature_branch",
                    lambda: {
                        "status": "rsigma",
                        "gate_passed": False,
                        "primary_blocker": "R_Sigma_solution_certificate",
                    },
                ),
            ),
            real_state_builder=lambda: {
                "gate_passed": False,
                "bao_chi2_evaluated": False,
                "missing_real_active_inputs": ["active_RSigma_solution_certificate"],
                "fixture_result_is_not_physical_result": True,
                "pipeline_evaluable_with_strict_inputs": True,
                "blocker": "real inputs incomplete",
                "next_required": [],
            },
        )

        self.assertEqual(payload["calculator_status"], "ready_for_strict_inputs")
        self.assertEqual(payload["next_physical_target"], "R_Sigma_solution_certificate")


if __name__ == "__main__":
    unittest.main()
