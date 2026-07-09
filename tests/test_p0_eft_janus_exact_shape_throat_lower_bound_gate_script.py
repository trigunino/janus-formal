import unittest

from janus_lab.janus_phase_space_occupation_search import (
    exact_shape_throat_lower_bound_payload,
)


class JanusExactShapeThroatLowerBoundGateTests(unittest.TestCase):
    def test_published_shape_has_nonzero_lower_bound(self):
        payload = exact_shape_throat_lower_bound_payload()

        self.assertGreater(payload["a_min_over_a0"], 0.0)
        self.assertTrue(payload["consequences"]["removes_a_zero_integral_divergence"])

    def test_published_sn_branch_does_not_reach_drag_epoch(self):
        payload = exact_shape_throat_lower_bound_payload()

        self.assertAlmostEqual(payload["z_max"], 5.74712643678, places=6)
        self.assertFalse(payload["consequences"]["reaches_standard_drag_redshift"])
        self.assertFalse(payload["consequences"]["published_SN_branch_sufficient_for_BAO_drag"])


if __name__ == "__main__":
    unittest.main()
