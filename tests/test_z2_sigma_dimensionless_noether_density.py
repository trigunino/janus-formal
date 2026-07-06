import math
import unittest

from src.janus_lab.z2_sigma_dimensionless_noether_density import (
    dimensionless_noether_density_r3,
    hubble_volume_noether_density,
)


class Z2SigmaDimensionlessNoetherDensityTest(unittest.TestCase):
    def test_rp3_density_factor(self):
        payload = dimensionless_noether_density_r3(2.0, quotient_spatial_slice="RP3")
        self.assertAlmostEqual(
            payload["baryon_number_density0_times_Rcurv3_Z2Sigma"],
            2.0 / math.pi**2,
        )

    def test_s3_paired_leaf_density_factor(self):
        payload = dimensionless_noether_density_r3(
            2.0,
            quotient_spatial_slice="S3_paired_leaf_representative",
        )
        self.assertAlmostEqual(
            payload["baryon_number_density0_times_Rcurv3_Z2Sigma"],
            1.0 / math.pi**2,
        )

    def test_rejects_bad_charge(self):
        with self.assertRaisesRegex(ValueError, "positive and finite"):
            dimensionless_noether_density_r3(0.0)

    def test_hubble_volume_density(self):
        payload = hubble_volume_noether_density(8.0, 2.0)
        self.assertAlmostEqual(
            payload["baryon_number_density0_times_Hubble_volume_Z2Sigma"],
            1.0,
        )


if __name__ == "__main__":
    unittest.main()
