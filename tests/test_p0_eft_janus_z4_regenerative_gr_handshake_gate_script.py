import unittest

from scripts.build_p0_eft_janus_z4_regenerative_gr_handshake_gate import build_payload


class P0EFTJanusZ4RegenerativeGRHandshakeGateTests(unittest.TestCase):
    def test_regenerative_gr_handshake_without_likelihoods(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "janus-z4-regenerative-gr-handshake-gate")
        self.assertEqual(payload["source_of_spectra"], "regenerated")
        self.assertEqual(payload["lambda_T"], 0.0)
        self.assertEqual(payload["lambda_E"], 0.0)
        self.assertFalse(payload["Z4_delta_enabled"])
        self.assertTrue(payload["C_l_not_D_l"])
        self.assertTrue(payload["TE_sign_preserved"])
        self.assertTrue(payload["ell_indexing_preserved"])
        self.assertTrue(payload["cl_pp_convention_is_C_L_phiphi"])
        self.assertTrue(payload["theory_vector_matches_reference"])
        self.assertTrue(payload["regenerative_gr_handshake_passed"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
