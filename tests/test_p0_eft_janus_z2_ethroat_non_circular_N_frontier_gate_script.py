import unittest

from scripts.build_p0_eft_janus_z2_ethroat_non_circular_N_frontier_gate import (
    build_payload,
)


class EThroatNonCircularNFrontierGateTests(unittest.TestCase):
    def test_no_current_non_circular_selector(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["N_selected_non_circularly"])
        self.assertEqual(payload["accepted_non_circular_selectors"], [])

    def test_horizon_entropy_is_rejected_as_circular(self):
        route = build_payload()["routes"]["horizon_entropy"]

        self.assertTrue(route["gives_N_1e120"])
        self.assertFalse(route["non_circular"])
        self.assertIn("H0", route["circular_inputs"])

    def test_best_remaining_frontiers_are_state_count_or_tqft(self):
        payload = build_payload()

        self.assertIn("microcanonical_state_count", payload["best_remaining_frontiers"])
        self.assertIn("topological_qft_partition_function", payload["best_remaining_frontiers"])


if __name__ == "__main__":
    unittest.main()
