import unittest

from scripts.build_p0_eft_janus_z2_sigma_collar_tubular_neighborhood_gate import build_payload


class P0EFTJanusZ2SigmaCollarTubularNeighborhoodGateTests(unittest.TestCase):
    def test_collar_tubular_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["collar_tubular_neighborhood_ledger_declared"])
        self.assertTrue(payload["declared"]["sigma_smooth_embedded_throat_gate_declared"])
        self.assertTrue(payload["declared"]["collar_neighborhood_bibliography_checked"])
        self.assertTrue(payload["declared"]["tubular_neighborhood_bibliography_checked"])
        self.assertTrue(payload["standard_collar_tubular_theorems_available"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")
        self.assertIn("normal_tube", payload["formulas"])

    def test_collar_tubular_closure_remains_blocked(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["sigma_smooth_embedded_derived"])
        self.assertFalse(payload["closure"]["normal_bundle_derived"])
        self.assertFalse(payload["closure"]["collar_tubular_neighborhood_ready"])
        self.assertFalse(payload["collar_tubular_neighborhood_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["upstream_frontiers"]["sigma_smooth_embedded_throat"]["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertIn("pass_sigma_smooth_embedded_throat_gate", payload["next_required"])
        self.assertIn("feed_result_to_resolved_tunnel_smooth_atlas_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
