from __future__ import annotations

import unittest

import numpy as np

from janus_lab.cosebis import (
    cosebis_en_from_xi,
    evaluate_tplus,
    log_cosebis_filters,
)


class CosebisTests(unittest.TestCase):
    def test_log_filters_satisfy_constraints_and_orthonormality(self) -> None:
        filters = log_cosebis_filters(3, samples=256)
        theta = np.geomspace(0.5, 300.0, 50000)

        values = [evaluate_tplus(item, theta) for item in filters]

        for value in values:
            self.assertLess(abs(float(np.trapezoid(theta * value, theta))), 1e-4)
            self.assertLess(abs(float(np.trapezoid(theta**3 * value, theta))), 1.0)
        for i, left in enumerate(values):
            for j, right in enumerate(values):
                inner = float(np.trapezoid(theta * left * right, theta))
                self.assertAlmostEqual(inner, 1.0 if i == j else 0.0, places=2)

    def test_cosebis_operator_returns_zero_for_zero_xi(self) -> None:
        filter_ = log_cosebis_filters(1, samples=128)[0]
        theta = np.geomspace(0.5, 300.0, 256)
        zeros = np.zeros_like(theta)

        self.assertAlmostEqual(cosebis_en_from_xi(theta, zeros, zeros, filter_), 0.0)

    def test_cosebis_operator_rejects_mismatched_arrays(self) -> None:
        filter_ = log_cosebis_filters(1, samples=128)[0]
        theta = np.geomspace(0.5, 300.0, 256)

        with self.assertRaisesRegex(ValueError, "matching one-dimensional"):
            cosebis_en_from_xi(theta, np.zeros(3), np.zeros_like(theta), filter_)


if __name__ == "__main__":
    unittest.main()
