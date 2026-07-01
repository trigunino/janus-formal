from __future__ import annotations

import unittest

import numpy as np

from scripts.build_kids1000_janus_holst_weyl_cosebis import build_payload, janus_holst_weyl_power_factory


class KiDS1000JanusHolstWeylCosebisTests(unittest.TestCase):
    def test_holst_weyl_power_is_positive_and_k_dependent(self) -> None:
        _, power = janus_holst_weyl_power_factory(amplitude=1.0e-9)
        k = np.asarray([[0.1, 1.0, 10.0]])
        z = np.asarray([[0.5, 0.5, 0.5]])
        values = power(k, z)

        self.assertTrue(np.all(values >= 0.0))
        self.assertNotEqual(float(values[0, 0]), float(values[0, 1]))

    def test_builds_scale_cut_vector_but_blocks_prediction_claim(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["dimension"], 75)
        self.assertEqual(payload["weyl_power_provenance"], "janus_holst_growth_shape_with_declared_primordial_amplitude")
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["chi2_ready"])


if __name__ == "__main__":
    unittest.main()
