import math
import unittest

from scripts.build_p0_eft_janus_z2_published_exact_solution_scale_frontier_gate import (
    alpha_from_h0,
    h_shape,
    build_payload,
)


class PublishedExactSolutionScaleFrontierGateTests(unittest.TestCase):
    def test_h_shape_matches_direct_formula(self):
        u = 2.0
        self.assertAlmostEqual(h_shape(u), math.sinh(2.0 * u) / math.cosh(u) ** 4)

    def test_alpha_from_h0_is_h_shape_over_h0(self):
        self.assertAlmostEqual(alpha_from_h0(2.0, 5.0), h_shape(2.0) / 5.0)

    def test_live_gate_blocks_without_alpha_or_h0(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["shape_closed"])
        self.assertTrue(payload["absolute_scale_requires_alpha_or_H0_or_clock"])


if __name__ == "__main__":
    unittest.main()
