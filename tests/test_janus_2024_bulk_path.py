import unittest

import numpy as np

from janus_lab.janus_2024_bulk_path import build_cited_bulk_reference_path
from janus_lab.janus_2024_cited_calibration import (
    published_janus_2024_cited_calibration,
)


class Janus2024BulkObservablePathTests(unittest.TestCase):
    def setUp(self):
        calibration = published_janus_2024_cited_calibration()
        self.path = build_cited_bulk_reference_path(
            reference=calibration.to_reference(),
            q0=calibration.q0,
            h0_s_inv=calibration.h0_s_inv,
            alpha_seconds=calibration.alpha_seconds,
        )

    def test_bulk_path_is_not_proxy(self):
        self.assertAlmostEqual(self.path.redshift_grid()[-1], 0.0)
        self.assertGreater(self.path.redshift_grid()[0], 4.0)

    def test_bulk_path_exposes_determinant_bridge(self):
        bridge = self.path.determinant_bridge()
        self.assertEqual(bridge.shape, self.path.x0.shape)
        self.assertTrue(np.all(bridge > 0.0))

    def test_bulk_path_exposes_normalized_e_plus(self):
        self.assertAlmostEqual(self.path.e_plus(0.0), 1.0)
        self.assertGreater(self.path.e_plus(1.0), 0.0)
        self.assertTrue(np.all(self.path.a_minus > 0.0))


if __name__ == "__main__":
    unittest.main()
