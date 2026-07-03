import unittest

from scripts.build_p0_eft_janus_z2_sigma_effective_background_closure_gate import build_payload


class P0EFTJanusZ2SigmaEffectiveBackgroundClosureGateTests(unittest.TestCase):
    def test_effective_background_equations_are_structurally_derived(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["effective_background_lock_closed"])
        self.assertTrue(payload["background_equations_derived"])
        self.assertTrue(payload["lock"]["effective_friedmann_equation_derived"])
        self.assertTrue(payload["lock"]["effective_acceleration_equation_derived"])
        self.assertTrue(payload["lock"]["effective_continuity_equation_derived"])
        self.assertFalse(payload["observational_parameters_fitted"])
        self.assertTrue(payload["legacy_lcdm_background_substitution_forbidden"])


if __name__ == "__main__":
    unittest.main()
