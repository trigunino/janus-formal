import unittest

from scripts.build_p0_eft_janus_z2_sigma_spinor_boundary_projection_map_gate import build_payload


class P0EFTJanusZ2SigmaSpinorBoundaryProjectionMapGateTests(unittest.TestCase):
    def test_spinor_boundary_projection_map_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["spinor_boundary_projection_map_ledger_declared"])
        self.assertTrue(payload["declared"]["APS_projection_bibliography_checked"])
        self.assertTrue(payload["declared"]["local_boundary_projection_bibliography_checked"])
        self.assertTrue(payload["declared"]["no_free_boundary_phase"])
        self.assertIn("flux_projection_domain", payload["upstream_frontiers"])
        self.assertIn("sigma_aps_pin_lift", payload["upstream_frontiers"])
        self.assertIn("boundary_spinor_restriction", payload["upstream_frontiers"])
        self.assertIn("tangent_normal_orientation", payload["upstream_frontiers"])
        self.assertIn("projective_gluing_normal_orientation_sign", payload["upstream_frontiers"])
        self.assertIn("local_mit_reflecting_projector", payload["upstream_frontiers"])
        self.assertTrue(payload["closure"]["Z2_coorientation_sign_ready"])
        self.assertTrue(payload["closure"]["Z2_normal_orientation_ready"])
        self.assertTrue(payload["closure"]["Sigma_APS_boundary_Pin_lift_closed"])
        self.assertTrue(payload["partial_subchannels"]["Z2_coorientation_sign"]["ready"])
        self.assertTrue(payload["partial_subchannels"]["Z2_normal_orientation_sign"]["ready"])
        self.assertTrue(payload["partial_subchannels"]["Sigma_APS_Pin_lift"]["ready"])
        self.assertTrue(payload["partial_subchannels"]["local_MIT_projector"]["ready"])
        self.assertTrue(payload["nearest_spinor_projection_frontier"]["diagnostic_only"])

    def test_projection_map_waits_for_active_boundary_data(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["boundary_spinor_restriction_ready"])
        self.assertFalse(payload["closure"]["Sigma_boundary_spinor_data_ready"])
        self.assertTrue(payload["closure"]["Sigma_APS_boundary_Pin_lift_closed"])
        self.assertTrue(payload["closure"]["Z2_normal_orientation_ready"])
        self.assertTrue(payload["closure"]["unit_normal_Clifford_action_ready"])
        self.assertTrue(payload["closure"]["projection_idempotent_ready"])
        self.assertTrue(payload["closure"]["projection_self_adjoint_ready"])
        self.assertFalse(payload["spinor_boundary_projection_map_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")
        self.assertEqual(
            payload["upstream_frontiers"]["tangent_normal_orientation"]["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertIn("derive_boundary_spinor_data_from_plus_minus_spinor_bundles", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
