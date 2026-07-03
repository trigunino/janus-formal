import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_number_normalization_gate import build_payload


class P0EFTJanusZ2SigmaDiracNumberNormalizationGateTests(unittest.TestCase):
    def test_number_normalization_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_number_normalization_ledger_declared"])
        self.assertTrue(payload["declared"]["Dirac_current_charge_integral_declared"])
        self.assertIn("plus_charge", payload["formulas"])

    def test_number_normalization_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_charge_fixed_by_action_or_topology"])
        self.assertFalse(payload["closure"]["number_normalizations_ready"])
        self.assertFalse(payload["dirac_number_normalization_ready"])
        self.assertIn("derive_N_plus_from_active_spinor_boundary_data", payload["next_required"])
        self.assertIn("propagate_number_normalization_to_density_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
