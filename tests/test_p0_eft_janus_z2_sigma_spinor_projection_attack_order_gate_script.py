import unittest

from scripts.build_p0_eft_janus_z2_sigma_spinor_projection_attack_order_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaSpinorProjectionAttackOrderGateTests(unittest.TestCase):
    def test_attack_order_blocks_on_active_embedding_and_normals_first(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")
        self.assertEqual(
            payload["upstream_frontiers"]["tangent_normal_orientation"]["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertFalse(payload["closure"]["spinor_boundary_projection_map_ready"])
        self.assertTrue(payload["no_free_boundary_phase"])
        self.assertTrue(payload["no_archived_z4_projection"])


if __name__ == "__main__":
    unittest.main()
