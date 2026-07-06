import unittest

from src.janus_lab.z2_sigma_density_normalization import (
    baryon_density_from_hubble_volume_invariant,
    baryon_density_from_r3_invariant,
)


class Z2SigmaDensityNormalizationTest(unittest.TestCase):
    def test_r3_route(self):
        self.assertEqual(baryon_density_from_r3_invariant(8.0, 2.0), 1.0)

    def test_hubble_route(self):
        value = baryon_density_from_hubble_volume_invariant(1.0, 299792.458)
        self.assertGreater(value, 0.0)

    def test_rejects_bad_inputs(self):
        with self.assertRaisesRegex(ValueError, "positive and finite"):
            baryon_density_from_r3_invariant(0.0, 1.0)


if __name__ == "__main__":
    unittest.main()
