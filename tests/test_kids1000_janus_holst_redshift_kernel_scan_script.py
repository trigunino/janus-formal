from __future__ import annotations

import unittest

import numpy as np

from scripts.build_kids1000_janus_holst_redshift_kernel_scan import (
    build_payload,
    default_kernel_power_grid,
    redshift_projection_factor,
)


class KiDS1000JanusHolstRedshiftKernelScanTests(unittest.TestCase):
    def test_default_kernel_power_grid_contains_no_extra_factor(self) -> None:
        self.assertIn(0.0, default_kernel_power_grid())

    def test_redshift_projection_factor_preserves_shape(self) -> None:
        factor = redshift_projection_factor(1.0)
        values = factor(np.asarray([0.0, 1.0]))

        self.assertEqual(values.shape, (2,))

    def test_payload_is_diagnostic_for_requested_powers(self) -> None:
        payload = build_payload([0.0, 1.0])

        self.assertEqual(payload["dimension"], 75)
        self.assertEqual(len(payload["rows"]), 2)
        self.assertFalse(payload["prediction_ready"])


if __name__ == "__main__":
    unittest.main()
