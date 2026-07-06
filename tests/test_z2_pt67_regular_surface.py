from __future__ import annotations

import unittest
from math import sqrt

from src.janus_lab.z2_pt67_regular_surface import (
    pt67_metric_block,
    pt67_regular_surface_geometry,
)


class Z2PT67RegularSurfaceTests(unittest.TestCase):
    def test_metric_block_is_regular_at_sigma(self) -> None:
        first = pt67_metric_block(1.0, 1.0, sheet_epsilon=-1)
        second = pt67_metric_block(1.0, 1.0, sheet_epsilon=1)

        self.assertEqual(first["A_TT"], 2.0)
        self.assertEqual(first["B_RR_positive_symbol"], 0.0)
        self.assertEqual(first["C_TR"], -1.0)
        self.assertEqual(second["C_TR"], 1.0)
        self.assertEqual(first["det_TR_block"], -1.0)

    def test_regular_surface_exports_h_and_local_k(self) -> None:
        payload = pt67_regular_surface_geometry()

        self.assertFalse(payload["regularity_at_sigma"]["induced_surface_degenerate"])
        self.assertTrue(payload["regularity_at_sigma"]["regular_hK_pipeline_allowed"])
        self.assertEqual(payload["unit_normal"]["normal_norm"], -1.0)
        self.assertAlmostEqual(payload["extrinsic_curvature_local"]["K_TT"], 1.0 / sqrt(2.0))
        self.assertAlmostEqual(payload["extrinsic_curvature_local"]["K_thetatheta"], sqrt(2.0))
        self.assertFalse(payload["raccord_to_regular_sigma_pipeline"]["DeltaK_plus_minus_ready"])


if __name__ == "__main__":
    unittest.main()
