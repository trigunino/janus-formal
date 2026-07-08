import unittest

from scripts.build_p0_eft_janus_bridge_state_law_candidate_discriminator_gate import build_payload


class JanusBridgeStateLawCandidateDiscriminatorTests(unittest.TestCase):
    def test_composite_path_is_selected_without_alpha_fit(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["chi_LL_selected_no_fit"])
        self.assertTrue(payload["rules"]["no_direct_alpha_fit"])
        self.assertTrue(payload["rules"]["no_single_route_promotion"])
        self.assertEqual(payload["next_gate"], "P0EFTJanusBridgeStateLawCompositeClosureGate")

    def test_no_individual_route_is_sufficient(self):
        payload = build_payload()

        self.assertEqual(len(payload["routes"]), 3)
        self.assertTrue(all(not row["sufficient_alone"] for row in payload["routes"]))


if __name__ == "__main__":
    unittest.main()
