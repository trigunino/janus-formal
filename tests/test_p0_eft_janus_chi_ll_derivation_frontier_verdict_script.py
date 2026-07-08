import unittest

from scripts.build_p0_eft_janus_chi_ll_derivation_frontier_verdict_gate import (
    build_payload,
)


class JanusChiLLDerivationFrontierVerdictTests(unittest.TestCase):
    def test_frontier_reduces_to_charge_normalization(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["chi_LL_selected_no_fit"])
        self.assertEqual(
            payload["frontier_reduced_to"],
            "worldvolume_charge_normalization_or_boundary_state_law",
        )
        self.assertTrue(payload["closed_subresults"]["WILL_action_power_p_half"])

    def test_only_real_next_moves_are_explicit(self):
        payload = build_payload()
        moves = " ".join(payload["only_real_next_moves"])

        self.assertIn("derive q_LL", moves)
        self.assertIn("PT boundary state", moves)
        self.assertIn("explicit state sector", moves)


if __name__ == "__main__":
    unittest.main()
