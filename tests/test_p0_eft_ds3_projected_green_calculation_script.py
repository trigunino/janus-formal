from __future__ import annotations

import unittest

from scripts.build_p0_eft_ds3_projected_green_calculation import build_payload, s3_spectral_response


class P0EFTDS3ProjectedGreenCalculationTests(unittest.TestCase):
    def test_spectral_response_is_positive(self) -> None:
        self.assertGreater(s3_spectral_response(cutoff_epsilon=0.1, l_max=64), 0.0)

    def test_payload_keeps_value_slip_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "regulated-spectral-green-scheme-dependent")
        self.assertTrue(payload["scheme_dependent"])
        self.assertFalse(payload["green_kernel_equals_three_halves_H_proved"])
        self.assertFalse(payload["value_slip_ready"])


if __name__ == "__main__":
    unittest.main()
