import unittest

import numpy as np

from janus_lab import JanusExpansion, comoving_distance_mpc, e_cpl, e_lcdm
from janus_lab.models import (
    janus_distance_modulus_proxy,
    janus_q0_from_u0,
    janus_u0_from_q0,
)


class ExpansionModelTests(unittest.TestCase):
    def test_lcdm_is_normalized_today(self):
        self.assertAlmostEqual(e_lcdm(0.0), 1.0)

    def test_cpl_is_normalized_today(self):
        self.assertAlmostEqual(e_cpl(0.0, w0=-0.8, wa=-0.5), 1.0)

    def test_janus_is_normalized_today(self):
        model = JanusExpansion(u0=4.0)
        self.assertAlmostEqual(model.e(0.0), 1.0)

    def test_janus_q0_roundtrip(self):
        u0 = 1.6
        q0 = janus_q0_from_u0(u0)
        self.assertAlmostEqual(janus_u0_from_q0(q0), u0)

    def test_janus_sn_proxy_is_finite(self):
        values = janus_distance_modulus_proxy(np.array([0.1, 1.0]), q0=-0.087)
        self.assertTrue(np.all(np.isfinite(values)))

    def test_janus_rejects_too_large_redshift(self):
        model = JanusExpansion(u0=0.5)
        with self.assertRaises(ValueError):
            model.e(model.z_max + 0.1)

    def test_comoving_distance_increases(self):
        z = np.array([0.1, 0.5, 1.0])
        d = comoving_distance_mpc(z, e_lcdm, samples=256)
        self.assertTrue(np.all(np.diff(d) > 0))


if __name__ == "__main__":
    unittest.main()
