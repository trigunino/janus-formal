import unittest

import numpy as np

from janus_lab.z2_sigma_sound_ruler import evaluate_rd_z2sigma_mpc


class Z2SigmaSoundRulerTests(unittest.TestCase):
    def test_sound_ruler_integrates_supplied_active_functions_only(self):
        h = lambda z: 70.0 * np.sqrt(0.3 * (1.0 + z) ** 3 + 0.7)
        cs = lambda z: np.full_like(z, 299792.458 / np.sqrt(3.0), dtype=float)

        rd = evaluate_rd_z2sigma_mpc(h, cs, z_d_z2sigma=1060.0, z_max=1.0e5, samples=256)

        self.assertTrue(np.isfinite(rd))
        self.assertGreater(rd, 0.0)

    def test_sound_ruler_rejects_missing_or_unphysical_inputs(self):
        h = lambda z: np.full_like(z, 70.0, dtype=float)
        cs = lambda z: np.full_like(z, 100000.0, dtype=float)

        with self.assertRaises(ValueError):
            evaluate_rd_z2sigma_mpc(h, cs, z_d_z2sigma=0.0)
        with self.assertRaises(ValueError):
            evaluate_rd_z2sigma_mpc(h, cs, z_d_z2sigma=10.0, z_max=5.0)
        with self.assertRaises(ValueError):
            evaluate_rd_z2sigma_mpc(lambda z: -h(z), cs, z_d_z2sigma=10.0, samples=32)


if __name__ == "__main__":
    unittest.main()
