import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    visible_matter_jordan_frame_pullback_attempt_payload,
)


class JanusVisibleMatterJordanFramePullbackAttemptGateTests(unittest.TestCase):
    def test_visible_clock_fixed_but_cusp_not_predictive(self):
        payload = visible_matter_jordan_frame_pullback_attempt_payload()
        self.assertTrue(payload["visible_clock_fixed"])
        self.assertFalse(payload["weyl_cusp_predictive"])
        self.assertFalse(payload["closed_now"])


if __name__ == "__main__":
    unittest.main()
