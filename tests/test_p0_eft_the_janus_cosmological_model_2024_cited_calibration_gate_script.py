import unittest

from scripts.build_p0_eft_the_janus_cosmological_model_2024_cited_calibration_gate import (
    build_payload,
)


class Janus2024CitedCalibrationGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = build_payload()

    def test_gate_materializes_absolute_normalization(self):
        payload = self.payload
        self.assertEqual(
            payload["status"],
            "the-janus-cosmological-model-2024-cited-calibration-gate",
        )
        self.assertTrue(payload["absolute_normalization_contract_ready"])
        self.assertTrue(payload["paper_grade_absolute_sector_normalization_inputs_ready"])
        self.assertTrue(payload["cited_calibration_not_no_fit"])
        self.assertEqual(payload["published_q0"], -0.087)
        self.assertEqual(payload["published_h0_km_s_mpc"], 70.0)


if __name__ == "__main__":
    unittest.main()
