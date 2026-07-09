import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    bimetric_scale_ratio_clock_attempt_payload,
)


class JanusBimetricScaleRatioClockAttemptGateTests(unittest.TestCase):
    def test_ratio_route_has_inputs_but_no_unique_omega(self):
        payload = bimetric_scale_ratio_clock_attempt_payload()
        self.assertTrue(payload["checks"]["two_scale_factors_available"])
        self.assertFalse(payload["checks"]["omega_defined_as_bimetric_ratio"])
        self.assertFalse(payload["closed_now"])


if __name__ == "__main__":
    unittest.main()
