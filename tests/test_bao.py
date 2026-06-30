import unittest

import numpy as np

from janus_lab.bao import bao_prediction, janus_bao_prediction, planck_like_scale
from janus_lab.models import e_lcdm
from janus_lab import JanusExpansion


class BaoTests(unittest.TestCase):
    def test_planck_like_scale_is_positive(self):
        self.assertGreater(planck_like_scale(), 0.0)

    def test_bao_predictions_are_positive(self):
        scale = planck_like_scale()
        for quantity in ["DM_over_rs", "DH_over_rs", "DV_over_rs"]:
            value = bao_prediction(0.7, quantity, e_lcdm, scale=scale, samples=128)
            self.assertTrue(np.isfinite(value))
            self.assertGreater(value, 0.0)

    def test_unknown_quantity_rejected(self):
        with self.assertRaises(ValueError):
            bao_prediction(0.7, "bad_quantity", e_lcdm, scale=planck_like_scale())

    def test_janus_bao_predictions_are_positive(self):
        model = JanusExpansion.from_q0(-0.087)
        value = janus_bao_prediction(0.7, "DM_over_rs", model, scale=planck_like_scale())
        self.assertTrue(np.isfinite(value))
        self.assertGreater(value, 0.0)


if __name__ == "__main__":
    unittest.main()
