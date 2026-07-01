from __future__ import annotations

import unittest

import numpy as np

from janus_lab.kink_source import (
    kink_jump_amplitude,
    kink_source_status,
    validate_kink_source_provenance,
)


class KinkSourceTests(unittest.TestCase):
    def test_symbolic_scaffold_computes_product(self) -> None:
        jump = kink_jump_amplitude(
            np.asarray([0.1, 1.0]),
            np.asarray([0.5, 1.0]),
            np.asarray([2.0, 4.0]),
            coefficient=lambda k, a: 3.0 + 0.0 * k + 0.0 * a,
            alpha=0.25,
            provenance="symbolic_scaffold",
        )

        np.testing.assert_allclose(jump, np.asarray([1.5, 3.0]))

    def test_forbidden_kids_or_fit_provenance_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            validate_kink_source_provenance("kids_pair23")
        with self.assertRaises(ValueError):
            validate_kink_source_provenance("late_fit_from_residuals")

    def test_status_promotes_only_source_derived_closure(self) -> None:
        self.assertFalse(
            kink_source_status(
                skink_coefficient_derived=True,
                alpha_janus_derived=True,
                provenance="symbolic_scaffold",
            )["prediction_ready"]
        )
        self.assertTrue(
            kink_source_status(
                skink_coefficient_derived=True,
                alpha_janus_derived=True,
                provenance="source_derived_holst_junction",
            )["prediction_ready"]
        )


if __name__ == "__main__":
    unittest.main()
