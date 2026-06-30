import unittest

import numpy as np

from janus_lab.statistics import (
    fixed_prediction_chi_square,
    validate_data_vector_and_covariance,
    weighted_linear_fit,
)


class StatisticsTests(unittest.TestCase):
    def test_weighted_linear_fit_recovers_coefficients(self):
        x = np.array([0.0, 1.0, 2.0, 3.0])
        design = np.column_stack([np.ones_like(x), x])
        observed = 2.0 + 3.0 * x
        covariance = np.eye(len(x))

        coeffs, prediction, chi2 = weighted_linear_fit(design, observed, covariance)

        self.assertTrue(np.allclose(coeffs, [2.0, 3.0]))
        self.assertTrue(np.allclose(prediction, observed))
        self.assertAlmostEqual(chi2, 0.0)

    def test_fixed_prediction_chi_square_uses_full_covariance(self):
        result = fixed_prediction_chi_square(
            "fixed",
            np.asarray([1.0, 2.0]),
            np.asarray([1.0, 1.0]),
            np.asarray([[2.0, 0.5], [0.5, 1.0]]),
        )

        self.assertEqual(result.n_params, 0)
        self.assertGreater(result.chi2, 0.0)

    def test_likelihood_rejects_non_positive_covariance(self):
        with self.assertRaises(ValueError):
            validate_data_vector_and_covariance(
                np.asarray([1.0]),
                np.asarray([1.0]),
                np.asarray([[0.0]]),
            )


if __name__ == "__main__":
    unittest.main()
