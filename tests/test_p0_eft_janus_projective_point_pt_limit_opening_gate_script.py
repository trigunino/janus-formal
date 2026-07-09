import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    projective_point_pt_limit_opening_payload,
)


class JanusProjectivePointPTLimitOpeningGateTests(unittest.TestCase):
    def test_sigma_obligations_are_removed(self):
        payload = projective_point_pt_limit_opening_payload()
        self.assertFalse(payload["active_geometry"]["finite_throat_sigma"])
        self.assertIn("R_Sigma selection", payload["removed_obligations"])
        self.assertIn("singular/projective initial condition", payload["new_or_remaining_obligations"])


if __name__ == "__main__":
    unittest.main()
