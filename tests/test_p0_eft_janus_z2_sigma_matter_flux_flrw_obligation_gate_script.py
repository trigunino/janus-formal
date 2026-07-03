import unittest

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_flrw_obligation_gate import build_payload


class P0EFTJanusZ2SigmaMatterFluxFLRWObligationGateTests(unittest.TestCase):
    def test_flux_method_is_imported_from_thin_shell_formalism(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["matter_flux_method_ready"])
        self.assertIn("T_munu", payload["formulas"]["flux_one_form"])
        self.assertTrue(payload["method"]["transparency_condition_declared"])

    def test_active_matter_flux_reduction_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["FLRW_matter_flux_reduced"])
        self.assertFalse(payload["closure"]["matter_flux_rho_p_of_a_ready"])
        self.assertFalse(payload["matter_flux_FLRW_closure_ready"])
        self.assertIn("decide_or_derive_transparency_condition_for_tunnel_throat", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
