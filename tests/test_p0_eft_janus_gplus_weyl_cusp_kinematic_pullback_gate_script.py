import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    gplus_weyl_cusp_kinematic_pullback_payload,
)


class JanusGPlusWeylCuspKinematicPullbackGateTests(unittest.TestCase):
    def test_kinematic_pullback_closed_not_dynamic(self):
        payload = gplus_weyl_cusp_kinematic_pullback_payload()
        self.assertTrue(payload["kinematic_pullback_closed"])
        self.assertFalse(payload["predictive_dynamics_closed"])
        self.assertEqual(payload["formulas"]["scale_factor"], "a_plus = Omega * a_hat")


if __name__ == "__main__":
    unittest.main()
