import unittest

import numpy as np

from janus_lab.z2_sigma_cartan_ghy import (
    make_cartan_ghy_components_from_plus_minus_extrinsic_curvature,
    make_cartan_ghy_components_over_rho_crit0,
)


class Z2SigmaCartanGHYTests(unittest.TestCase):
    def test_cartan_ghy_components_use_active_delta_k_inputs(self):
        rho, pressure = make_cartan_ghy_components_over_rho_crit0(
            lambda a: 2.0 * a,
            lambda a: 5.0 * a,
            z2_orientation_sign=1.0,
            kappa_rho_crit0=10.0,
        )
        a = np.asarray([1.0, 0.5])

        np.testing.assert_allclose(rho(a), [0.6, 0.3])
        np.testing.assert_allclose(pressure(a), [0.1, 0.05])

    def test_cartan_ghy_components_respect_z2_orientation(self):
        rho_plus, _ = make_cartan_ghy_components_over_rho_crit0(
            lambda a: a,
            lambda a: a,
            z2_orientation_sign=1.0,
            kappa_rho_crit0=3.0,
        )
        rho_minus, _ = make_cartan_ghy_components_over_rho_crit0(
            lambda a: a,
            lambda a: a,
            z2_orientation_sign=-1.0,
            kappa_rho_crit0=3.0,
        )
        a = np.asarray([1.0])

        np.testing.assert_allclose(rho_minus(a), -rho_plus(a))

    def test_cartan_ghy_components_compose_plus_minus_curvatures(self):
        rho, pressure = make_cartan_ghy_components_from_plus_minus_extrinsic_curvature(
            k_s_plus_of_a=lambda a: 3.0 * a,
            k_s_minus_of_a=lambda a: 1.0 * a,
            k_tau_plus_of_a=lambda a: 5.0 * a,
            k_tau_minus_of_a=lambda a: 2.0 * a,
            z2_orientation_sign=-1.0,
            kappa_rho_crit0=10.0,
        )
        a = np.asarray([1.0, 0.5])

        np.testing.assert_allclose(rho(a), [-0.6, -0.3])
        np.testing.assert_allclose(pressure(a), [1.0 / 10.0, 0.5 / 10.0])

    def test_cartan_ghy_components_reject_bad_inputs(self):
        with self.assertRaises(ValueError):
            make_cartan_ghy_components_over_rho_crit0(
                lambda a: a,
                lambda a: a,
                z2_orientation_sign=0.0,
                kappa_rho_crit0=1.0,
            )
        with self.assertRaises(ValueError):
            make_cartan_ghy_components_over_rho_crit0(
                lambda a: a,
                lambda a: a,
                z2_orientation_sign=1.0,
                kappa_rho_crit0=0.0,
            )

        rho, _ = make_cartan_ghy_components_over_rho_crit0(
            lambda a: np.asarray([1.0]),
            lambda a: a,
            z2_orientation_sign=1.0,
            kappa_rho_crit0=1.0,
        )
        with self.assertRaises(ValueError):
            rho(np.asarray([1.0, 0.5]))


if __name__ == "__main__":
    unittest.main()
