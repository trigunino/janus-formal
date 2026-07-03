import unittest

from scripts.build_p0_eft_janus_z2_sigma_holst_nieh_yan_flrw_obligation_gate import build_payload


class P0EFTJanusZ2SigmaHolstNiehYanFLRWObligationGateTests(unittest.TestCase):
    def test_holst_nieh_yan_method_is_imported_from_bibliography(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["holst_nieh_yan_method_ready"])
        self.assertTrue(payload["method"]["torsion_pullback_on_Sigma_gate_declared"])
        self.assertIn("Banerjee 2010, arXiv:1002.0669", payload["primary_sources_checked"])
        self.assertTrue(payload["guards"]["do_not_import_torsionless_Holst_as_nonzero"])

    def test_active_flrw_torsion_reduction_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["FLRW_torsion_irreducible_decomposition_ready"])
        self.assertFalse(payload["closure"]["Holst_Nieh_Yan_FLRW_stress_reduced"])
        self.assertFalse(payload["holst_nieh_yan_FLRW_closure_ready"])
        self.assertIn("pass_torsion_pullback_on_Sigma_gate", payload["next_required"])
        self.assertIn("derive_FLRW_irreducible_torsion_pullback_on_Sigma", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
