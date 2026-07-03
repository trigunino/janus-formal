import unittest

from scripts.build_p0_eft_janus_z2_sigma_embedding_gauge_equation_gate import build_payload


class P0EFTJanusZ2SigmaEmbeddingGaugeEquationGateTests(unittest.TestCase):
    def test_gauge_equations_are_ready_without_observational_fit(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["embedding_gauge_equations_declared"])
        self.assertTrue(payload["embedding_gauge_equations_ready"])
        self.assertTrue(payload["declared"]["observational_gauge_fit_forbidden"])

    def test_full_embedding_closure_still_requires_throat_radius_law(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["throat_radius_law_still_required"])
        self.assertFalse(payload["closure"]["X_plus_minus_of_a_determined"])
        self.assertFalse(payload["embedding_gauge_full_closure_ready"])
        self.assertIn("derive_R_Sigma_of_a_from_resolved_projective_tunnel_geometry", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
