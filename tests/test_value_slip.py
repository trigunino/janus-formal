from __future__ import annotations

import unittest

import numpy as np

from janus_lab.value_slip import (
    derivative_slip_source_shape,
    scaffold_status,
    sigma_from_mu_and_eta_slip,
    validate_value_slip_provenance,
    value_slip_from_green_kernel,
)


class ValueSlipTests(unittest.TestCase):
    def test_forbidden_kids_provenance_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            validate_value_slip_provenance("kids_delta_z")

    def test_derivative_slip_source_shape_broadcasts(self) -> None:
        k = np.asarray([0.0, 1.0])
        source = derivative_slip_source_shape(k, np.asarray([1.0]), np.asarray([0.2]), np.asarray([0.5]))

        self.assertTrue(np.allclose(source, [0.0, 0.05]))

    def test_value_slip_requires_computed_green_kernel(self) -> None:
        with self.assertRaises(ValueError):
            value_slip_from_green_kernel(
                np.asarray([1.0]),
                np.asarray([1.0]),
                np.asarray([1.0]),
                lambda k, a: np.ones_like(k),
                green_kernel_computed=False,
                provenance="source_derived_green_kernel",
            )

    def test_value_slip_from_green_kernel_multiplies_source(self) -> None:
        value = value_slip_from_green_kernel(
            np.asarray([2.0]),
            np.asarray([1.0]),
            np.asarray([1.0]),
            lambda k, a: 3.0 * np.ones_like(k),
            green_kernel_computed=True,
            provenance="source_derived_green_kernel",
        )

        self.assertTrue(np.allclose(value, [6.0]))

    def test_sigma_from_mu_and_eta_slip(self) -> None:
        sigma = sigma_from_mu_and_eta_slip(np.asarray([2.0]), np.asarray([0.5]))

        self.assertTrue(np.allclose(sigma, [1.5]))

    def test_scaffold_status_only_predicts_for_source_derived_kernel(self) -> None:
        self.assertFalse(scaffold_status(green_kernel_computed=False, provenance="symbolic_scaffold")["prediction_ready"])
        self.assertTrue(
            scaffold_status(green_kernel_computed=True, provenance="source_derived_green_kernel")["prediction_ready"]
        )


if __name__ == "__main__":
    unittest.main()
