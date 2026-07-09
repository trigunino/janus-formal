import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    conformal_pt_boundary_matching_attempt_payload,
)


class JanusConformalPTBoundaryMatchingAttemptGateTests(unittest.TestCase):
    def test_removes_finite_throat_mismatch_but_not_clock_law(self):
        payload = conformal_pt_boundary_matching_attempt_payload()
        self.assertTrue(payload["checks"]["finite_sigma_radius_removed"])
        self.assertTrue(payload["checks"]["c1_throat_velocity_mismatch_removed"])
        self.assertFalse(payload["checks"]["conformal_lapse_or_clock_law_derived"])
        self.assertFalse(payload["closed_now"])

    def test_same_late_cosh_requires_wrong_q0_for_z1000(self):
        payload = conformal_pt_boundary_matching_attempt_payload()
        self.assertAlmostEqual(payload["required_q0_if_same_late_cosh_branch"], -0.0005)
        self.assertFalse(payload["checks"]["same_late_cosh_shape_compatible"])


if __name__ == "__main__":
    unittest.main()
