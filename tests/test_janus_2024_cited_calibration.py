import unittest

from janus_lab.janus_2024_cited_calibration import (
    published_janus_2024_cited_calibration,
)


class Janus2024CitedCalibrationTests(unittest.TestCase):
    def test_published_bundle_has_expected_signs(self):
        calibration = published_janus_2024_cited_calibration()
        contract = calibration.to_normalization_contract()
        self.assertLess(calibration.e_global_j, 0.0)
        self.assertGreater(contract.rho_plus0_kg_m3, 0.0)
        self.assertLess(contract.rho_minus0_kg_m3, 0.0)
        self.assertAlmostEqual(
            contract.rho_minus0_over_rho_plus0,
            -19.0,
        )

    def test_cited_bundle_has_positive_scale_and_negative_global_energy(self):
        calibration = published_janus_2024_cited_calibration()
        self.assertGreater(calibration.alpha_seconds, 0.0)
        self.assertGreater(calibration.alpha_m, 0.0)
        self.assertLess(calibration.e_global_mass_kg, 0.0)


if __name__ == "__main__":
    unittest.main()
