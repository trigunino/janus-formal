from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_bin_factor_audit import build_payload, fit_bin_factors


class KiDS1000JanusHolstBinFactorAuditTests(unittest.TestCase):
    def test_fit_bin_factors_recovers_simple_ratios(self) -> None:
        rows = [
            {"bin1": 1, "bin2": 1, "pair_to_global_amplitude_ratio": 4.0},
            {"bin1": 1, "bin2": 2, "pair_to_global_amplitude_ratio": 6.0},
            {"bin1": 2, "bin2": 2, "pair_to_global_amplitude_ratio": 9.0},
        ]

        factors, residuals, rms = fit_bin_factors(rows, bin_count=2)

        self.assertAlmostEqual(factors[0], 2.0)
        self.assertAlmostEqual(factors[1], 3.0)
        self.assertLess(rms, 1.0e-12)
        self.assertEqual(len(residuals), 3)

    def test_payload_is_diagnostic(self) -> None:
        payload = build_payload()

        self.assertEqual(len(payload["bin_factors"]), 5)
        self.assertFalse(payload["prediction_ready"])


if __name__ == "__main__":
    unittest.main()
