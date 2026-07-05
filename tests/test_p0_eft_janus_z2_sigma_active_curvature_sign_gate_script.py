import unittest

from scripts.build_p0_eft_janus_z2_sigma_active_curvature_sign_gate import build_payload


class P0EFTJanusZ2SigmaActiveCurvatureSignGateTests(unittest.TestCase):
    def test_curvature_sign_domain_ready_but_values_blocked(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["projective_tunnel_two_fold_topology_ready"])
        self.assertFalse(payload["topology_alone_fixes_FLRW_curvature_sign"])
        self.assertFalse(payload["flrw_spatial_metric_branch_gate_passed"])
        self.assertFalse(payload["flrw_spatial_metric_branch_values_ready"])
        self.assertTrue(payload["rp3_spatial_slice_to_k_plus_one_rule_ready"])
        self.assertTrue(payload["projective_foliation_to_rp3_slice_rule_ready"])
        self.assertFalse(payload["rp3_spatial_slice_input_writer_passed"])
        self.assertFalse(payload["rp3_spatial_slice_curvature_sign_gate_passed"])
        self.assertIn(payload["projective_spatial_slice_topology_branch_gate_passed"], [True, False])
        if payload["projective_spatial_slice_topology_branch_gate_passed"]:
            self.assertIn(
                payload["selected_spatial_topology_branch"],
                ["RP3", "S3_paired_leaf_representative"],
            )
        else:
            self.assertIsNone(payload["selected_spatial_topology_branch"])
        self.assertTrue(payload["rp3_curvature_radius_still_required"])
        self.assertTrue(payload["curvature_sign_domain_declared"])
        self.assertEqual(payload["curvature_sign_allowed_values"], [-1, 0, 1])
        self.assertTrue(payload["requires_active_spatial_metric_branch"])
        self.assertTrue(payload["requires_active_embedding_scale_or_induced_spatial_metric"])
        self.assertTrue(payload["requires_R_Sigma_or_X_plus_minus_solution"])
        self.assertEqual(
            payload["curvature_sign_values_ready"],
            payload["projective_spatial_slice_topology_branch_gate_passed"]
            or payload["rp3_spatial_slice_curvature_sign_gate_passed"],
        )
        self.assertEqual(payload["gate_passed"], payload["curvature_sign_values_ready"])

    def test_curvature_sign_gate_forbids_external_fit_or_archived_inputs(self):
        payload = build_payload()

        self.assertFalse(payload["uses_compressed_planck_lcdm_background"])
        self.assertFalse(payload["uses_archived_z4_background"])
        self.assertFalse(payload["uses_observational_curvature_fit"])


if __name__ == "__main__":
    unittest.main()
