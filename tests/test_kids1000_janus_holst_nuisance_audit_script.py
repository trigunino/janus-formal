from __future__ import annotations

import unittest

import numpy as np

from scripts.build_kids1000_janus_holst_nuisance_audit import build_payload, nuisance_design


class KiDS1000JanusHolstNuisanceAuditTests(unittest.TestCase):
    def test_nuisance_design_has_amplitude_pair_and_mode_templates(self) -> None:
        rows = [
            {"bin1": 1, "bin2": 1, "angbin": 1},
            {"bin1": 1, "bin2": 2, "angbin": 2},
            {"bin1": 2, "bin2": 2, "angbin": 3},
        ]
        labels, design = nuisance_design(rows, np.asarray([2.0, 3.0, 4.0]))

        self.assertEqual(labels, ["amplitude", "pair_bin_tilt", "mode_tilt"])
        self.assertEqual(design.shape, (3, 3))
        self.assertTrue(np.allclose(design[:, 0], [2.0, 3.0, 4.0]))
        self.assertAlmostEqual(float(np.mean(design[:, 1] / design[:, 0])), 0.0)

    def test_payload_is_diagnostic_not_prediction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["dimension"], 75)
        self.assertEqual(len(payload["models"]), 4)
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["chi2_claim_ready"])


if __name__ == "__main__":
    unittest.main()
