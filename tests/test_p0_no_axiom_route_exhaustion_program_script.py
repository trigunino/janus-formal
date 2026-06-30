from __future__ import annotations

import unittest

from scripts.build_p0_no_axiom_route_exhaustion_program import build_payload, render_markdown


class P0NoAxiomRouteExhaustionProgramTests(unittest.TestCase):
    def test_program_launches_no_axiom_routes(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "no-axiom-route-exhaustion-launched")
        self.assertTrue(payload["no_axiom_policy"])
        self.assertFalse(payload["new_axiom_adopted"])
        self.assertFalse(payload["prediction_ready"])
        self.assertEqual(payload["route_count"], 6)
        self.assertEqual(payload["agent_track_count"], 4)
        self.assertEqual(
            payload["route_a_integrability_audit_artifact"],
            "p0_route_a_integrability_nullspace_audit",
        )
        self.assertFalse(payload["route_a_integrability_unique_selector"])
        self.assertEqual(
            payload["route_b_sheetwise_kinetic_artifact"],
            "p0_stueckelberg_sheetwise_kinetic_transport_gate",
        )
        self.assertFalse(payload["route_b_single_global_phi_l_required"])
        self.assertEqual(
            payload["route_c_geometric_exotic_artifact"],
            "p0_route_c_geometric_exotic_completion_gate",
        )
        self.assertEqual(
            payload["route_c_bf_holonomy_priority_artifact"],
            "p0_route_c_bf_holonomy_priority_attack",
        )
        self.assertEqual(
            payload["route_c_phi_r_identity_artifact"],
            "p0_route_c_phi_r_curvature_identity_gate",
        )
        self.assertEqual(
            payload["route_c_phi_r_selector_probe_artifact"],
            "p0_route_c_phi_r_relative_curvature_selector_probe",
        )
        self.assertEqual(
            payload["route_c_small_loop_holonomy_probe_artifact"],
            "p0_route_c_small_loop_holonomy_numeric_probe",
        )
        self.assertEqual(
            payload["route_c_path_rule_selector_matrix_artifact"],
            "p0_route_c_path_rule_selector_matrix",
        )
        self.assertEqual(
            payload["route_c_two_path_nonunique_l_probe_artifact"],
            "p0_route_c_two_path_nonunique_l_probe",
        )
        self.assertEqual(
            payload["route_c_janus_path_rule_source_derivation_artifact"],
            "p0_route_c_janus_path_rule_source_derivation_gate",
        )
        self.assertEqual(
            payload["route_c_boundary_gauge_unique_l_obstruction_artifact"],
            "p0_route_c_boundary_gauge_unique_l_obstruction",
        )
        self.assertEqual(
            payload["route_c_no_path_rule_underselection_theorem_artifact"],
            "p0_route_c_no_path_rule_underselection_theorem",
        )
        self.assertEqual(
            payload["route_c_indirect_path_rule_source_audit_artifact"],
            "p0_route_c_indirect_path_rule_source_audit",
        )
        self.assertEqual(
            payload["route_c_action_noether_path_rule_derivation_artifact"],
            "p0_route_c_action_noether_path_rule_derivation_attempt",
        )
        self.assertEqual(
            payload["route_c_pt_geometry_path_rule_audit_artifact"],
            "p0_route_c_pt_geometry_path_rule_audit",
        )
        self.assertEqual(
            payload["route_c_pt_selector_derivation_attempt_artifact"],
            "p0_route_c_pt_selector_derivation_attempt",
        )
        self.assertEqual(
            payload["route_c_pt_only_no_selector_certificate_artifact"],
            "p0_route_c_pt_only_no_selector_certificate",
        )
        self.assertEqual(
            payload["route_c_pt_fixed_path_extension_candidate_artifact"],
            "p0_route_c_pt_fixed_path_extension_candidate_gate",
        )
        self.assertEqual(
            payload["route_c_ordered_path_action_source_derivation_artifact"],
            "p0_route_c_ordered_path_action_source_derivation_gate",
        )
        self.assertEqual(
            payload["route_c_minimal_spath_extension_axiom_artifact"],
            "p0_route_c_minimal_spath_extension_axiom_gate",
        )
        self.assertEqual(
            payload["route_c_spath_euler_lagrange_artifact"],
            "p0_route_c_spath_euler_lagrange_equations",
        )
        self.assertEqual(
            payload["route_c_spath_lorentz_tetrad_variation_artifact"],
            "p0_route_c_spath_lorentz_tetrad_variation_gate",
        )
        self.assertEqual(
            payload["route_c_spath_same_l_substitution_artifact"],
            "p0_route_c_spath_same_l_substitution_gate",
        )
        self.assertEqual(
            payload["route_c_spath_stability_screen_artifact"],
            "p0_route_c_spath_stability_screen",
        )
        self.assertEqual(
            payload["route_c_spath_scalar_density_completion_artifact"],
            "p0_route_c_spath_scalar_density_completion_gate",
        )
        self.assertEqual(
            payload["route_c_spath_cj_vj_invariant_filter_artifact"],
            "p0_route_c_spath_cj_vj_invariant_filter",
        )
        self.assertEqual(
            payload["route_c_spath_cj_vj_coefficient_underselection_artifact"],
            "p0_route_c_spath_cj_vj_coefficient_underselection_gate",
        )
        self.assertEqual(
            payload["route_c_spath_cj_vj_filter_rank_no_go_artifact"],
            "p0_route_c_spath_cj_vj_filter_rank_no_go",
        )
        self.assertEqual(
            payload["route_c_spath_cj_vj_nonlinear_local_no_go_artifact"],
            "p0_route_c_spath_cj_vj_nonlinear_local_no_go",
        )
        self.assertEqual(
            payload["route_c_spath_constraint_equation_classifier_artifact"],
            "p0_route_c_spath_constraint_equation_classifier",
        )
        self.assertEqual(
            payload["route_c_orbifold_pt_soldering_candidate_artifact"],
            "p0_orbifold_pt_soldering_candidate",
        )
        self.assertEqual(
            payload["route_c_orbifold_pt_action_variation_artifact"],
            "p0_orbifold_pt_action_variation_gate",
        )
        self.assertEqual(
            payload["route_c_orbifold_pt_source_current_artifact"],
            "p0_orbifold_pt_source_current_gate",
        )
        self.assertEqual(
            payload["route_c_orbifold_pt_defect_matching_artifact"],
            "p0_orbifold_pt_defect_matching_law_gate",
        )
        self.assertEqual(
            payload["route_c_orbifold_pt_bdefect_filter_artifact"],
            "p0_orbifold_pt_bdefect_action_filter",
        )
        self.assertEqual(
            payload["route_c_orbifold_pt_topological_defect_branch_artifact"],
            "p0_orbifold_pt_topological_defect_branch_gate",
        )
        self.assertEqual(
            payload["route_c_orbifold_pt_ktop_quantization_artifact"],
            "p0_orbifold_pt_ktop_quantization_gate",
        )
        self.assertEqual(
            payload["route_c_spath_metric_stress_variation_artifact"],
            "p0_route_c_spath_metric_stress_variation_gate",
        )
        self.assertEqual(
            payload["route_c_spath_bianchi_noether_artifact"],
            "p0_route_c_spath_bianchi_noether_gate",
        )
        self.assertEqual(payload["route_c_best_ranked_routes"], ["BF_connection", "holonomy"])
        self.assertEqual(
            payload["route_d_no_go_expansion_artifact"],
            "p0_local_low_derivative_scalar_tensor_no_go_expansion",
        )
        self.assertEqual(
            payload["route_d_no_go_structural_matrix_artifact"],
            "p0_route_d_no_go_structural_matrix",
        )
        self.assertEqual(
            payload["route_d_tensor_derivative_filter_artifact"],
            "p0_route_d_tensor_derivative_admissibility_filter",
        )
        self.assertEqual(
            payload["route_d_derivative_curvature_nullspace_artifact"],
            "p0_route_d_derivative_curvature_nullspace_gate",
        )
        self.assertEqual(
            payload["route_d_source_free_pde_nullspace_probe_artifact"],
            "p0_route_d_source_free_pde_nullspace_probe",
        )
        self.assertEqual(
            payload["route_d_source_free_boundary_no_go_argument_artifact"],
            "p0_route_d_source_free_boundary_no_go_argument",
        )
        self.assertEqual(
            payload["route_d_local_pde_no_selector_certificate_artifact"],
            "p0_route_d_local_pde_no_selector_certificate",
        )
        self.assertEqual(
            payload["route_d_source_derived_stf_operator_escape_artifact"],
            "p0_route_d_source_derived_stf_operator_escape_gate",
        )
        self.assertEqual(
            payload["route_d_stf_operator_construction_obstruction_artifact"],
            "p0_route_d_stf_operator_construction_obstruction",
        )
        self.assertEqual(
            payload["route_d_stf_no_go_closure_attempt_artifact"],
            "p0_route_d_stf_no_go_closure_attempt",
        )
        self.assertEqual(
            payload["zero_axiom_closure_decision_artifact"],
            "p0_zero_axiom_closure_decision_gate",
        )
        self.assertEqual(
            payload["minimal_nonrustine_extension_contract_artifact"],
            "p0_minimal_nonrustine_extension_contract",
        )
        self.assertEqual(
            payload["remaining_research_priority_queue_artifact"],
            "p0_remaining_research_priority_queue",
        )
        self.assertFalse(payload["route_d_full_theorem_proved"])

    def test_routes_cover_requested_search_space(self) -> None:
        routes = {row["route"] for row in build_payload()["routes"]}

        self.assertIn("integrability_frobenius", routes)
        self.assertIn("kinetic_sheet_vlasov", routes)
        self.assertIn("connection_holonomy", routes)
        self.assertIn("optimal_transport", routes)
        self.assertIn("local_no_go", routes)
        self.assertIn("nonlocal_kernel", routes)

    def test_agent_tracks_are_parallelizable(self) -> None:
        tracks = {row["agent_track"]: row for row in build_payload()["agent_tracks"]}

        self.assertEqual(set(tracks), {"integrability", "kinetic_sheet", "geometric_exotic", "local_no_go"})
        self.assertTrue(all(row["status"] == "launched" for row in tracks.values()))

    def test_markdown_is_practical(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("No-Axiom Route Exhaustion", markdown)
        self.assertIn("Route A integrability unique selector: False", markdown)
        self.assertIn("Route B single global phi/L required: False", markdown)
        self.assertIn("Route D full theorem proved: False", markdown)
        self.assertIn("No-axiom policy: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
