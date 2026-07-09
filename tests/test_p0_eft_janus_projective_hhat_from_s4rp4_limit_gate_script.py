import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    projective_hhat_from_s4rp4_limit_payload,
)


class JanusProjectiveHhatFromS4RP4LimitGateTests(unittest.TestCase):
    def test_hhat_geometry_not_dynamics(self):
        payload = projective_hhat_from_s4rp4_limit_payload()
        self.assertTrue(payload["hhat_geometry_closed"])
        self.assertFalse(payload["hhat_dynamics_closed"])


if __name__ == "__main__":
    unittest.main()
