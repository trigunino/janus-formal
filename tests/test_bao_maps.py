from __future__ import annotations

import unittest

import numpy as np

from janus_lab.bao_maps import (
    AnisotropicPowerLawScale,
    AnisotropicSqrtAScale,
    QuantityLinearScale,
    dv_from_dm_dh,
    gauge_weighted_open_marker,
    janus_c4_gauge_prediction,
    janus_c5_redshift_prediction,
    janus_c6_common_ruler_prediction,
    janus_c7_anisotropic_linear_ruler_prediction,
    redshift_power_remap,
    sqrt_a_scale,
)
from janus_lab.bao import janus_bao_prediction
from janus_lab.models import JanusExpansion


class BaoMapTests(unittest.TestCase):
    def test_sqrt_a_scale(self) -> None:
        self.assertAlmostEqual(sqrt_a_scale(3.0, amplitude=2.0), 1.0)

    def test_quantity_linear_scale(self) -> None:
        scale = QuantityLinearScale(
            dm_intercept=10.0,
            dm_slope=-1.0,
            dh_intercept=20.0,
            dh_slope=-2.0,
            dv_intercept=30.0,
            dv_slope=-3.0,
        )

        self.assertAlmostEqual(scale.scale(2.0, "DM_over_rs"), 8.0)
        self.assertAlmostEqual(scale.scale(2.0, "DH_over_rs"), 16.0)
        self.assertAlmostEqual(scale.scale(2.0, "DV_over_rs"), 24.0)

    def test_dv_relation(self) -> None:
        value = dv_from_dm_dh(dm_over_rs=4.0, dh_over_rs=2.0, z=1.0)
        self.assertAlmostEqual(value, float(np.cbrt(32.0)))

    def test_anisotropic_sqrt_a_derives_dv_amplitude(self) -> None:
        scale = AnisotropicSqrtAScale(dm_amplitude=8.0, dh_amplitude=1.0)

        self.assertAlmostEqual(scale.dv_amplitude, 4.0)
        self.assertAlmostEqual(scale.scale(3.0, "DM_over_rs"), 4.0)
        self.assertAlmostEqual(scale.scale(3.0, "DH_over_rs"), 0.5)
        self.assertAlmostEqual(scale.scale(3.0, "DV_over_rs"), 2.0)

    def test_anisotropic_power_law_derives_dv(self) -> None:
        scale = AnisotropicPowerLawScale(
            dm_amplitude=8.0,
            dm_power=-1.0,
            dh_amplitude=1.0,
            dh_power=2.0,
        )

        self.assertAlmostEqual(scale.scale(3.0, "DM_over_rs"), 2.0)
        self.assertAlmostEqual(scale.scale(3.0, "DH_over_rs"), 16.0)
        self.assertAlmostEqual(scale.scale(3.0, "DV_over_rs"), 4.0)

    def test_gauge_marker_zero_power_matches_m18_marker(self) -> None:
        model = JanusExpansion.from_q0(-0.087)
        z = 0.7
        ue = model.u_of_z(z)
        expected = np.sinh(2.0 * (model.u0 - ue))

        self.assertAlmostEqual(gauge_weighted_open_marker(z, model, 0.0), expected)

    def test_c4_zero_powers_matches_base_bao(self) -> None:
        model = JanusExpansion.from_q0(-0.087)
        z = 0.7
        scale = 30.0

        self.assertAlmostEqual(
            janus_c4_gauge_prediction(z, "DM_over_rs", model, scale, 0.0, 0.0),
            janus_bao_prediction(z, "DM_over_rs", model, scale),
        )
        self.assertAlmostEqual(
            janus_c4_gauge_prediction(z, "DH_over_rs", model, scale, 0.0, 0.0),
            janus_bao_prediction(z, "DH_over_rs", model, scale),
        )

    def test_redshift_power_remap_identity(self) -> None:
        z = np.asarray([0.1, 1.0, 2.0])

        np.testing.assert_allclose(redshift_power_remap(z, 1.0), z)

    def test_c5_gamma_one_matches_base_bao(self) -> None:
        model = JanusExpansion.from_q0(-0.087)
        z = 0.7
        scale = 30.0

        for quantity in ["DM_over_rs", "DH_over_rs", "DV_over_rs"]:
            self.assertAlmostEqual(
                janus_c5_redshift_prediction(
                    z,
                    quantity,
                    model,
                    scale,
                    gamma=1.0,
                    compression_z="observed",
                ),
                janus_bao_prediction(z, quantity, model, scale),
            )

    def test_c6_zero_power_matches_base_bao(self) -> None:
        model = JanusExpansion.from_q0(-0.087)
        z = 0.7
        scale = 30.0

        for quantity in ["DM_over_rs", "DH_over_rs", "DV_over_rs"]:
            self.assertAlmostEqual(
                janus_c6_common_ruler_prediction(
                    z,
                    quantity,
                    model,
                    scale,
                    ruler_power=0.0,
                ),
                janus_bao_prediction(z, quantity, model, scale),
            )

    def test_c7_constant_rulers_match_base_bao(self) -> None:
        model = JanusExpansion.from_q0(-0.087)
        z = 0.7
        scale = 30.0

        for quantity in ["DM_over_rs", "DH_over_rs", "DV_over_rs"]:
            self.assertAlmostEqual(
                janus_c7_anisotropic_linear_ruler_prediction(
                    z,
                    quantity,
                    model,
                    dm_intercept=scale,
                    dm_slope=0.0,
                    dh_intercept=scale,
                    dh_slope=0.0,
                ),
                janus_bao_prediction(z, quantity, model, scale),
            )


if __name__ == "__main__":
    unittest.main()
