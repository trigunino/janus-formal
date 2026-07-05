import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_charge_boundary_projection_gate import build_payload


class P0EFTJanusZ2SigmaDiracChargeBoundaryProjectionGateTests(unittest.TestCase):
    def test_charge_projection_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_charge_boundary_projection_ledger_declared"])
        self.assertTrue(payload["declared"]["projected_Dirac_matter_current_gate_declared"])
        self.assertIn("projected_dirac_matter_current", payload["upstream_frontiers"])
        self.assertIn("spinor_bundle_projection", payload["upstream_frontiers"])
        self.assertIn("projected_charge", payload["formulas"])
        self.assertTrue(payload["declared"]["observational_fit_forbidden"])
        self.assertEqual(
            payload["primary_blocker"],
            "R_Sigma_solution_certificate",
        )

    def test_charge_projection_waits_for_current_and_spinors(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["projected_Dirac_current_ready"])
        self.assertFalse(payload["closure"]["spinor_projection_ready"])
        self.assertFalse(payload["upstream_frontiers"]["projected_dirac_matter_current"]["ready"])
        self.assertFalse(payload["upstream_frontiers"]["spinor_bundle_projection"]["ready"])
        self.assertFalse(payload["dirac_charge_boundary_projection_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertIn("pass_projected_Dirac_matter_current_gate", payload["next_required"])
        self.assertIn("feed_result_to_Dirac_number_normalization_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
