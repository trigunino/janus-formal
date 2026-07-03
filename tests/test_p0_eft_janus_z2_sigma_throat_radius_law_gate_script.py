import unittest

from scripts.build_p0_eft_janus_z2_sigma_throat_radius_law_gate import build_payload


class P0EFTJanusZ2SigmaThroatRadiusLawGateTests(unittest.TestCase):
    def test_throat_radius_problem_and_candidate_ansatz_are_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["throat_radius_law_problem_declared"])
        self.assertIn("R_Sigma(a) = a * R0", payload["candidate_laws"]["comoving_throat"])
        self.assertTrue(payload["declared"]["observational_fit_for_radius_forbidden"])

    def test_candidate_ansatz_is_not_promoted_without_janus_derivation(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["Janus_action_or_topology_derives_radius_law"])
        self.assertFalse(payload["closure"]["R_Sigma_of_a_ready"])
        self.assertFalse(payload["throat_radius_law_closure_ready"])
        self.assertIn("derive_R_Sigma_of_a_from_resolved_projective_tunnel", payload["next_required"][0])


if __name__ == "__main__":
    unittest.main()
