import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_radial_block_gate import build_payload


class P0EFTJanusZ2SigmaCountertermRadialBlockGateTests(unittest.TestCase):
    def test_counterterm_radial_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["counterterm_radial_ledger_declared"])
        self.assertTrue(payload["declared"]["Sigma_counterterm_uniqueness_imported"])
        self.assertTrue(payload["declared"]["counterterm_density_expansion_gate_declared"])
        self.assertIn("L_ct", payload["structural_formula"])

    def test_counterterm_reduction_waits_for_explicit_density(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["counterterm_density_expansion_ready"])
        self.assertFalse(payload["closure"]["explicit_counterterm_density_ready"])
        self.assertFalse(payload["upstream_frontiers"]["density_expansion"]["ready"])
        self.assertFalse(payload["counterterm_radial_block_reduced"])
        self.assertFalse(payload["counterterm_radial_block_of_a_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["primary_blocker"],
            "tetrad_residual_channel",
        )
        self.assertEqual(
            payload["upstream_frontiers"]["density_expansion"]["primary_blocker"],
            "tetrad_residual_channel",
        )
        self.assertIn("counterterm_density_expansion_ready = false", payload["current_frontier"])
        self.assertIn("pass_counterterm_density_expansion_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
