import unittest

import numpy as np

from janus_lab.z2_sigma_extrinsic_curvature import (
    build_flrw_extrinsic_curvature_component_arrays,
    dynamic_spherical_shell_extrinsic_curvature_components,
    extrinsic_curvature_from_embedding_second_form,
    make_z2_oriented_extrinsic_curvature_jumps,
    reduce_flrw_extrinsic_curvature_components,
)


class Z2SigmaExtrinsicCurvatureTests(unittest.TestCase):
    def test_extrinsic_curvature_from_second_form_uses_active_geometry(self):
        radius = 2.0
        theta = 0.0
        tangents = np.asarray([[0.0, radius]])
        second = np.asarray([[[-radius, 0.0]]])
        christoffel = np.zeros((2, 2, 2))
        outward_normal = np.asarray([np.cos(theta), np.sin(theta)])

        k_ab = extrinsic_curvature_from_embedding_second_form(
            tangents,
            second,
            christoffel,
            outward_normal,
        )

        np.testing.assert_allclose(k_ab, [[radius]])

    def test_flrw_reduction_uses_spatial_trace_and_tau_component(self):
        k_ab = np.diag([2.0, 3.0, 6.0, 9.0])
        gamma_inv = np.diag([1.0, 0.5, 1.0 / 3.0])

        k_s, k_tau = reduce_flrw_extrinsic_curvature_components(k_ab, gamma_inv)

        self.assertAlmostEqual(k_s, 3.0)
        self.assertAlmostEqual(k_tau, 2.0)

    def test_flrw_component_arrays_evaluate_active_geometry_grid(self):
        def tangents(a):
            return np.eye(4)

        def second(a):
            tensor = np.zeros((4, 4, 4))
            tensor[0, 0, 0] = -2.0 * a
            tensor[1, 1, 0] = -3.0 * a
            tensor[2, 2, 0] = -6.0 * a
            tensor[3, 3, 0] = -9.0 * a
            return tensor

        zero_gamma = lambda a: np.zeros((4, 4, 4))
        normal = lambda a: np.asarray([1.0, 0.0, 0.0, 0.0])
        spatial_inv = lambda a: np.diag([1.0, 0.5, 1.0 / 3.0])

        k_s, k_tau = build_flrw_extrinsic_curvature_component_arrays(
            [0.5, 1.0],
            tangents,
            second,
            zero_gamma,
            normal,
            spatial_inv,
        )

        np.testing.assert_allclose(k_s, [1.5, 3.0])
        np.testing.assert_allclose(k_tau, [1.0, 2.0])

    def test_z2_oriented_jumps_use_active_plus_minus_curvatures(self):
        delta_s, delta_tau = make_z2_oriented_extrinsic_curvature_jumps(
            k_s_plus_of_a=lambda a: 3.0 * a,
            k_s_minus_of_a=lambda a: 1.0 * a,
            k_tau_plus_of_a=lambda a: 5.0 * a,
            k_tau_minus_of_a=lambda a: 2.0 * a,
            z2_orientation_sign=-1.0,
        )
        a = np.asarray([1.0, 0.5])

        np.testing.assert_allclose(delta_s(a), [2.0, 1.0])
        np.testing.assert_allclose(delta_tau(a), [3.0, 1.5])

    def test_z2_oriented_jumps_support_orientation_sum_convention(self):
        delta_s, _ = make_z2_oriented_extrinsic_curvature_jumps(
            k_s_plus_of_a=lambda a: a,
            k_s_minus_of_a=lambda a: 2.0 * a,
            k_tau_plus_of_a=lambda a: a,
            k_tau_minus_of_a=lambda a: a,
            z2_orientation_sign=1.0,
        )

        np.testing.assert_allclose(delta_s(np.asarray([1.0])), [3.0])

    def test_projective_orientation_does_not_zero_normal_reversal_jump(self):
        delta_s, delta_tau = make_z2_oriented_extrinsic_curvature_jumps(
            k_s_plus_of_a=lambda a: 3.0 * a,
            k_s_minus_of_a=lambda a: -3.0 * a,
            k_tau_plus_of_a=lambda a: 5.0 * a,
            k_tau_minus_of_a=lambda a: -5.0 * a,
            z2_orientation_sign=-1.0,
        )

        np.testing.assert_allclose(delta_s(np.asarray([1.0])), [6.0])
        np.testing.assert_allclose(delta_tau(np.asarray([1.0])), [10.0])

    def test_dynamic_spherical_shell_components_match_standard_formula(self):
        result = dynamic_spherical_shell_extrinsic_curvature_components(
            R=np.asarray([2.0]),
            R_dot=np.asarray([0.0]),
            R_ddot=np.asarray([0.5]),
            f_plus=np.asarray([4.0]),
            f_minus=np.asarray([9.0]),
            df_plus_dR=np.asarray([2.0]),
            df_minus_dR=np.asarray([4.0]),
            epsilon_plus=1.0,
            epsilon_minus=-1.0,
        )

        np.testing.assert_allclose(result["K_s_plus"], [1.0])
        np.testing.assert_allclose(result["K_s_minus"], [-1.5])
        np.testing.assert_allclose(result["K_tau_plus"], [0.75])
        np.testing.assert_allclose(result["K_tau_minus"], [-5.0 / 6.0])

    def test_z2_oriented_jumps_reject_bad_inputs(self):
        with self.assertRaises(ValueError):
            make_z2_oriented_extrinsic_curvature_jumps(
                lambda a: a,
                lambda a: a,
                lambda a: a,
                lambda a: a,
                z2_orientation_sign=0.0,
            )

        delta_s, _ = make_z2_oriented_extrinsic_curvature_jumps(
            k_s_plus_of_a=lambda a: np.asarray([1.0]),
            k_s_minus_of_a=lambda a: a,
            k_tau_plus_of_a=lambda a: a,
            k_tau_minus_of_a=lambda a: a,
            z2_orientation_sign=-1.0,
        )
        with self.assertRaises(ValueError):
            delta_s(np.asarray([1.0, 0.5]))

        with self.assertRaises(ValueError):
            delta_s(np.asarray([0.0]))

    def test_embedding_second_form_rejects_bad_shapes(self):
        with self.assertRaises(ValueError):
            extrinsic_curvature_from_embedding_second_form(
                tangent_vectors=np.ones((1, 2)),
                second_embedding=np.ones((1, 1, 3)),
                christoffel_symbols=np.zeros((2, 2, 2)),
                normal_covector=np.ones(2),
            )

    def test_flrw_reduction_rejects_bad_spatial_metric(self):
        with self.assertRaises(ValueError):
            reduce_flrw_extrinsic_curvature_components(np.eye(4), np.eye(2))

    def test_flrw_component_arrays_reject_bad_grid(self):
        with self.assertRaises(ValueError):
            build_flrw_extrinsic_curvature_component_arrays(
                [1.0, 0.5],
                lambda a: np.eye(4),
                lambda a: np.zeros((4, 4, 4)),
                lambda a: np.zeros((4, 4, 4)),
                lambda a: np.asarray([1.0, 0.0, 0.0, 0.0]),
                lambda a: np.eye(3),
            )


if __name__ == "__main__":
    unittest.main()
