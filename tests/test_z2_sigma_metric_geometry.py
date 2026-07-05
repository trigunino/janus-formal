import unittest

import numpy as np

from janus_lab.z2_sigma_metric_geometry import (
    christoffel_symbols_from_metric_derivatives,
    induced_metric_from_tangents,
    inverse_metric,
    normalize_level_set_normal_covector,
    normalize_timelike_contravariant_vectors,
    tangent_normal_contractions,
    vector_normal_contractions,
)


class Z2SigmaMetricGeometryTests(unittest.TestCase):
    def test_christoffel_symbols_match_polar_plane(self):
        r = 2.0
        metric = np.diag([1.0, r * r])
        inv = inverse_metric(metric)
        dg = np.zeros((2, 2, 2))
        dg[0, 1, 1] = 2.0 * r

        gamma = christoffel_symbols_from_metric_derivatives(inv, dg)

        self.assertAlmostEqual(gamma[0, 1, 1], -r)
        self.assertAlmostEqual(gamma[1, 0, 1], 1.0 / r)
        self.assertAlmostEqual(gamma[1, 1, 0], 1.0 / r)

    def test_normalize_level_set_normal_covector(self):
        inv = np.diag([1.0, 0.25])

        normal = normalize_level_set_normal_covector(
            np.asarray([1.0, 0.0]),
            inv,
            normal_norm_sign=1.0,
            orientation_sign=-1.0,
        )

        np.testing.assert_allclose(normal, [-1.0, 0.0])

    def test_induced_metric_from_tangents(self):
        metric = np.diag([1.0, 4.0])
        tangents = np.asarray([[0.0, 1.0]])

        induced = induced_metric_from_tangents(metric, tangents)

        np.testing.assert_allclose(induced, [[4.0]])

    def test_metric_primitives_reject_bad_inputs(self):
        with self.assertRaises(ValueError):
            inverse_metric(np.asarray([[1.0, 1.0], [0.0, 1.0]]))
        with self.assertRaises(ValueError):
            normalize_level_set_normal_covector(
                np.asarray([1.0, 0.0]),
                np.diag([-1.0, 1.0]),
                normal_norm_sign=1.0,
            )
        with self.assertRaises(ValueError):
            induced_metric_from_tangents(np.eye(2), np.ones((1, 3)))

    def test_normalize_timelike_contravariant_vectors(self):
        velocities = normalize_timelike_contravariant_vectors(
            [[[-4.0, 0.0], [0.0, 1.0]], [[-9.0, 0.0], [0.0, 1.0]]],
            [[1.0, 0.0], [1.0, 0.0]],
        )

        np.testing.assert_allclose(velocities, [[0.5, 0.0], [1.0 / 3.0, 0.0]])

    def test_normalize_timelike_rejects_spacelike_direction(self):
        with self.assertRaises(ValueError):
            normalize_timelike_contravariant_vectors(
                [[[-1.0, 0.0], [0.0, 1.0]]],
                [[0.0, 1.0]],
            )

    def test_vector_and_tangent_normal_contractions(self):
        metric = [[[-1.0, 0.0], [0.0, 1.0]], [[-1.0, 0.0], [0.0, 4.0]]]
        normal = [[0.0, 1.0], [0.0, 0.5]]

        u_dot_n = vector_normal_contractions(metric, [[1.0, 0.0], [1.0, 0.0]], normal)
        e_dot_n = tangent_normal_contractions(
            metric,
            [[[1.0, 0.0]], [[1.0, 0.0]]],
            normal,
        )

        np.testing.assert_allclose(u_dot_n, [0.0, 0.0])
        np.testing.assert_allclose(e_dot_n, [[0.0], [0.0]])


if __name__ == "__main__":
    unittest.main()
