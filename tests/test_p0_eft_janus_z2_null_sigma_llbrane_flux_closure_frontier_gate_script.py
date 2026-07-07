import unittest

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_flux_closure_frontier_gate import (
    build_payload,
)


class LLBraneFluxClosureFrontierGateTests(unittest.TestCase):
    def test_frontier_keeps_observations_blocked(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["ready_for_numeric_chi_LL"])
        self.assertFalse(payload["observation_allowed_now"])

    def test_frontier_reduces_to_three_independent_inputs(self):
        payload = build_payload()
        remaining = payload["remaining_independent_theory_inputs"]

        self.assertEqual(payload["minimal_remaining_count"], 3)
        self.assertIn("q_LL", remaining)
        self.assertIn("dimensionful_F2_0", remaining)
        self.assertIn("physical_area_gauge", remaining)

    def test_topology_and_matching_are_closed_without_rustine(self):
        closed = build_payload()["closed_without_rustine"]

        self.assertTrue(closed["S2_flux_integer_sector_supported"])
        self.assertTrue(closed["chi_composite_and_conserved"])
        self.assertTrue(closed["PT_negative_sign_and_bridge_matching"])


if __name__ == "__main__":
    unittest.main()
