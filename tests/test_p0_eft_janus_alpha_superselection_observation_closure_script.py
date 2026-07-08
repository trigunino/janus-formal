import unittest

from scripts.build_p0_eft_janus_alpha_superselection_observation_closure_gate import (
    build_payload,
)


class JanusAlphaSuperselectionObservationClosureTests(unittest.TestCase):
    def test_current_runner_closes_negative_for_proxy(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["sn_bao_runner_executed"])
        self.assertTrue(payload["primary_at_grid_boundary"])
        self.assertFalse(payload["interior_janus_sector_selected"])
        self.assertEqual(
            payload["classification"],
            "superselection_calibration_closes_negative_for_current_background_proxy",
        )


if __name__ == "__main__":
    unittest.main()
