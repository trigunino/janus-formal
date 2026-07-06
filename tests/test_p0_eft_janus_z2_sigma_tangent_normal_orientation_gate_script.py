import unittest

from scripts.build_p0_eft_janus_z2_sigma_tangent_normal_orientation_gate import build_payload


class P0EFTJanusZ2SigmaTangentNormalOrientationGateTests(unittest.TestCase):
    def test_tangent_normal_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["tangent_normal_orientation_ledger_declared"])
        self.assertTrue(payload["declared"]["active_embedding_from_radius_gate_declared"])
        self.assertTrue(payload["declared"]["tangent_frame_formula_declared"])
        self.assertTrue(payload["declared"]["unit_normal_formula_declared"])
        self.assertTrue(payload["declared"]["Z2_normal_orientation_declared"])
        self.assertTrue(payload["declared"]["projective_gluing_normal_orientation_sign_gate_declared"])
        self.assertTrue(payload["declared"]["embedding_tangent_frame_transport_gate_declared"])

    def test_orientation_remains_blocked_on_active_embedding(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["local_unit_tangent_normal_frame_ready"])
        self.assertTrue(payload["local_tangent_normal_orientation_ready"])
        self.assertFalse(payload["closure"]["active_Sigma_embedding_ready"])
        self.assertFalse(payload["closure"]["unit_normals_of_a_ready"])
        self.assertTrue(payload["closure"]["Z2_orientation_sign_fixed"])
        self.assertFalse(payload["active_tangent_normal_orientation_ready"])
        self.assertTrue(payload["tangent_normal_orientation_ready"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertEqual(
            payload["upstream_frontiers"]["active_tunnel_embedding_of_a"]["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertTrue(payload["active_embedding_not_claimed"])
        self.assertIn("use_local_unit_frame_for_boundary_spinor_projection", payload["next_required"])
        self.assertIn("keep_full_embedding_frames_blocked_until_R_Sigma_certificate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
