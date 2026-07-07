import unittest

from scripts.build_p0_eft_janus_z2_ethroat_remaining_non_circular_frontiers_gate import (
    build_payload,
)


class EThroatRemainingNonCircularFrontiersGateTests(unittest.TestCase):
    def test_no_remaining_frontier_currently_selects_N(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["N_selected_non_circularly"])
        self.assertIsNone(payload["accepted_non_circular_selector"])

    def test_microcanonical_route_requires_state_law(self):
        route = build_payload()["microcanonical_boundary_hilbert_space"]

        self.assertTrue(route["non_circular_if_closed"])
        self.assertFalse(route["ready"])
        self.assertIn("boundary_Hilbert_space_HSigma_derived", route["blocked_by"])
        self.assertIn("state_law_selects_macro_N_without_observation", route["blocked_by"])

    def test_tqft_route_requires_level_and_primitive_sector(self):
        route = build_payload()["janus_derived_tqft_level"]

        self.assertTrue(route["non_circular_if_closed"])
        self.assertFalse(route["ready"])
        self.assertIn("level_k_derived_without_area_or_H0", route["blocked_by"])
        self.assertIn("partition_function_selects_macro_N_without_observation", route["blocked_by"])


if __name__ == "__main__":
    unittest.main()
