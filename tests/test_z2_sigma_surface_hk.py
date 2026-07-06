from __future__ import annotations

import unittest

import numpy as np

from janus_lab.z2_sigma_surface_hk import (
    polynomial_surface_hk_isotropic_alpha_components,
    reduce_surface_hk_radial_geometry_tensors,
    riccati_normal_flow_radial_primitives,
    surface_hk_alpha_radial_from_isotropic_components,
)


class Z2SigmaSurfaceHKTests(unittest.TestCase):
    def test_isotropic_alpha_radial_contracts_time_and_three_spatial_components(self) -> None:
        result = surface_hk_alpha_radial_from_isotropic_components(
            sqrt_abs_h=[2.0],
            alpha_h_tau=[1.0],
            alpha_h_s=[2.0],
            alpha_k_tau=[3.0],
            alpha_k_s=[4.0],
            partial_R_h_tau=[5.0],
            partial_R_h_s=[6.0],
            partial_R_K_tau=[7.0],
            partial_R_K_s=[8.0],
        )

        np.testing.assert_allclose(result, [2.0 * (5.0 + 3.0 * 12.0 + 21.0 + 3.0 * 32.0)])

    def test_rejects_bad_shapes_and_measure(self) -> None:
        with self.assertRaises(ValueError):
            surface_hk_alpha_radial_from_isotropic_components(
                sqrt_abs_h=[0.0],
                alpha_h_tau=[1.0],
                alpha_h_s=[1.0],
                alpha_k_tau=[1.0],
                alpha_k_s=[1.0],
                partial_R_h_tau=[1.0],
                partial_R_h_s=[1.0],
                partial_R_K_tau=[1.0],
                partial_R_K_s=[1.0],
            )

    def test_polynomial_alpha_components_follow_isotropic_split(self) -> None:
        result = polynomial_surface_hk_isotropic_alpha_components(
            a0=1.0,
            a1=2.0,
            a2=3.0,
            a3=4.0,
            K_tau=[5.0],
            K_s=[7.0],
        )

        self.assertEqual(result["K_trace"].tolist(), [16.0])
        self.assertEqual(result["K_ab_Kab"].tolist(), [172.0])
        self.assertEqual(result["L_Sigma"].tolist(), [1489.0])
        self.assertEqual(result["alpha_K_tau"].tolist(), [-58.0])
        self.assertEqual(result["alpha_K_s"].tolist(), [154.0])
        self.assertEqual(result["alpha_h_tau"].tolist(), [-744.5 - 98.0 * 5.0 + 200.0])
        self.assertEqual(result["alpha_h_s"].tolist(), [744.5 - 98.0 * 7.0 - 392.0])

    def test_polynomial_alpha_components_reject_mismatched_curvatures(self) -> None:
        with self.assertRaises(ValueError):
            polynomial_surface_hk_isotropic_alpha_components(
                a0=1.0,
                a1=1.0,
                a2=1.0,
                a3=1.0,
                K_tau=[1.0, 2.0],
                K_s=[1.0],
            )

    def test_reduce_surface_hk_radial_geometry_tensors(self) -> None:
        result = reduce_surface_hk_radial_geometry_tensors(
            induced_metric_h_ab=[np.diag([-1.0, 4.0, 9.0, 16.0])],
            extrinsic_curvature_K_ab=[np.diag([2.0, 8.0, 18.0, 32.0])],
            partial_R_induced_metric_h_ab=[np.diag([3.0, 4.0, 9.0, 16.0])],
            partial_R_extrinsic_curvature_K_ab=[np.diag([5.0, 12.0, 27.0, 48.0])],
        )

        self.assertEqual(result["K_tau_values"].tolist(), [2.0])
        self.assertEqual(result["K_s_values"].tolist(), [2.0])
        self.assertEqual(result["partial_R_h_tau_values"].tolist(), [3.0])
        self.assertEqual(result["partial_R_h_s_values"].tolist(), [1.0])
        self.assertEqual(result["partial_R_K_tau_values"].tolist(), [5.0])
        self.assertEqual(result["partial_R_K_s_values"].tolist(), [3.0])

    def test_riccati_normal_flow_radial_primitives(self) -> None:
        result = riccati_normal_flow_radial_primitives(
            induced_metric_h_ab=[np.diag([1.0, 4.0])],
            extrinsic_curvature_K_ab=[np.diag([2.0, 8.0])],
            normal_riemann_R_nabn=[np.diag([3.0, 5.0])],
        )

        np.testing.assert_allclose(
            result["partial_R_induced_metric_h_ab"],
            [np.diag([4.0, 16.0])],
        )
        np.testing.assert_allclose(
            result["partial_R_extrinsic_curvature_K_ab"],
            [np.diag([7.0, 21.0])],
        )

        with self.assertRaises(ValueError):
            surface_hk_alpha_radial_from_isotropic_components(
                sqrt_abs_h=[1.0, 2.0],
                alpha_h_tau=[1.0],
                alpha_h_s=[1.0, 1.0],
                alpha_k_tau=[1.0, 1.0],
                alpha_k_s=[1.0, 1.0],
                partial_R_h_tau=[1.0, 1.0],
                partial_R_h_s=[1.0, 1.0],
                partial_R_K_tau=[1.0, 1.0],
                partial_R_K_s=[1.0, 1.0],
            )


if __name__ == "__main__":
    unittest.main()
