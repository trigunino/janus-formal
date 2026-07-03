import unittest

from scripts.build_p0_eft_janus_z2_sigma_plus_minus_dirac_action_local_reduction_gate import build_payload


class P0EFTJanusZ2SigmaPlusMinusDiracActionLocalReductionGateTests(unittest.TestCase):
    def test_local_reduction_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["plus_minus_dirac_action_local_reduction_ledger_declared"])
        self.assertTrue(payload["declared"]["kinetic_term_declared"])
        self.assertTrue(payload["declared"]["mass_bilinear_term_declared"])
        self.assertTrue(payload["declared"]["axial_torsion_coupling_declared"])
        self.assertIn("mass_bilinear_pm", payload["formulas"])

    def test_local_reduction_closure_remains_blocked(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_matter_action_ready"])
        self.assertFalse(payload["closure"]["plus_mass_bilinear_reduced"])
        self.assertFalse(payload["plus_minus_dirac_action_local_reduction_ready"])
        self.assertIn("feed_result_to_Dirac_mass_term_from_action_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
