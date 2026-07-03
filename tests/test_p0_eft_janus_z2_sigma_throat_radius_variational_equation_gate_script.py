import unittest

from scripts.build_p0_eft_janus_z2_sigma_throat_radius_variational_equation_gate import build_payload


class P0EFTJanusZ2SigmaThroatRadiusVariationalEquationGateTests(unittest.TestCase):
    def test_variational_radius_equation_is_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["throat_radius_variational_problem_declared"])
        self.assertTrue(payload["throat_radius_variational_equation_ready"])
        self.assertIn("delta S_Sigma", payload["variational_equation"])

    def test_radius_law_solution_is_not_claimed(self):
        payload = build_payload()

        self.assertTrue(payload["declared"]["topology_only_underdetermines_radius_law"])
        self.assertFalse(payload["equation"]["R_Sigma_equation_solved"])
        self.assertFalse(payload["equation"]["R_Sigma_of_a_ready"])
        self.assertFalse(payload["throat_radius_variational_closure_ready"])


if __name__ == "__main__":
    unittest.main()
