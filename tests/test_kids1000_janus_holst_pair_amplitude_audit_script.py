from __future__ import annotations

import unittest

import numpy as np

from scripts.build_kids1000_janus_holst_pair_amplitude_audit import build_payload, pair_amplitude_rows


class KiDS1000JanusHolstPairAmplitudeAuditTests(unittest.TestCase):
    def test_pair_amplitude_rows_return_one_row_per_pair(self) -> None:
        rows = [
            {"bin1": 1, "bin2": 1, "angbin": 1},
            {"bin1": 1, "bin2": 1, "angbin": 2},
            {"bin1": 1, "bin2": 2, "angbin": 1},
            {"bin1": 1, "bin2": 2, "angbin": 2},
        ]

        result = pair_amplitude_rows(rows, np.asarray([2.0, 4.0, 3.0, 6.0]), np.eye(4), np.asarray([1.0, 2.0, 1.0, 2.0]))

        self.assertEqual(len(result), 2)
        self.assertAlmostEqual(result[0]["pair_fit_chi2"], 0.0)

    def test_payload_is_diagnostic(self) -> None:
        payload = build_payload()

        self.assertEqual(len(payload["pair_rows"]), 15)
        self.assertFalse(payload["prediction_ready"])
        self.assertGreater(payload["pair23_ratio"], 0.0)


if __name__ == "__main__":
    unittest.main()
