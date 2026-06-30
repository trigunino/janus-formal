from __future__ import annotations

import unittest

import numpy as np

from janus_lab.initial_conditions import (
    bounded_anticorrelated_contrasts_3d,
    bounded_anticorrelated_contrasts_for_sigma_r_3d,
    displacement_from_contrast,
    displacement_from_contrast_3d,
    gaussian_random_field_2d,
    gaussian_random_field_3d,
    lattice_bodies_from_displacement,
    lattice_bodies_from_displacement_3d,
    lognormal_contrast_from_gaussian,
    paired_lognormal_contrasts_for_sigma_r_3d,
    paired_lognormal_sector_contrasts_3d,
    paired_sector_contrasts,
    paired_sector_contrasts_3d,
    sector_contrast_correlation,
    two_sector_lattice_initial_conditions,
    two_sector_lattice_initial_conditions_3d,
)
from janus_lab.field_statistics import sigma_r_3d
from janus_lab.signed_sector import Sector


class InitialConditionsTests(unittest.TestCase):
    def test_gaussian_field_is_reproducible_and_normalized(self) -> None:
        first = gaussian_random_field_2d((16, 16), 1.0, seed=123, target_rms=0.05)
        second = gaussian_random_field_2d((16, 16), 1.0, seed=123, target_rms=0.05)

        np.testing.assert_allclose(first, second)
        self.assertAlmostEqual(float(np.mean(first)), 0.0, places=15)
        self.assertAlmostEqual(float(np.sqrt(np.mean(first**2))), 0.05)

    def test_paired_sector_contrasts_are_anticorrelated(self) -> None:
        fields = paired_sector_contrasts((16, 16), 1.0, seed=7, target_rms=0.02)

        self.assertAlmostEqual(sector_contrast_correlation(fields), -1.0)
        np.testing.assert_allclose(fields.negative_contrast, -fields.positive_contrast)

    def test_gaussian_field_3d_is_reproducible_and_normalized(self) -> None:
        first = gaussian_random_field_3d((8, 8, 8), 1.0, seed=123, target_rms=0.05)
        second = gaussian_random_field_3d((8, 8, 8), 1.0, seed=123, target_rms=0.05)

        np.testing.assert_allclose(first, second)
        self.assertAlmostEqual(float(np.mean(first)), 0.0, places=15)
        self.assertAlmostEqual(float(np.sqrt(np.mean(first**2))), 0.05)

    def test_paired_sector_contrasts_3d_are_anticorrelated(self) -> None:
        fields = paired_sector_contrasts_3d((8, 8, 8), 1.0, seed=7, target_rms=0.02)

        self.assertAlmostEqual(sector_contrast_correlation(fields), -1.0)
        np.testing.assert_allclose(fields.negative_contrast, -fields.positive_contrast)

    def test_lognormal_contrast_is_density_safe(self) -> None:
        field = gaussian_random_field_3d((8, 8, 8), 1.0, seed=1, target_rms=1.0)

        contrast = lognormal_contrast_from_gaussian(field, amplitude=0.5)

        self.assertGreater(float(np.min(contrast)), -1.0)
        self.assertAlmostEqual(float(np.mean(contrast)), 0.0, places=15)

    def test_paired_lognormal_sector_contrasts_are_density_safe(self) -> None:
        field = gaussian_random_field_3d((8, 8, 8), 1.0, seed=1, target_rms=1.0)

        fields = paired_lognormal_sector_contrasts_3d(field, amplitude=0.5)

        self.assertGreater(float(np.min(fields.positive_contrast)), -1.0)
        self.assertGreater(float(np.min(fields.negative_contrast)), -1.0)
        self.assertLess(sector_contrast_correlation(fields), 0.0)

    def test_paired_lognormal_contrasts_for_sigma_r_hits_target(self) -> None:
        field = gaussian_random_field_3d((16, 16, 16), 1.0, seed=2, target_rms=1.0)

        fields, _ = paired_lognormal_contrasts_for_sigma_r_3d(
            field,
            box_size=1.0,
            radius=0.2,
            target_sigma=0.2,
        )

        self.assertAlmostEqual(
            sigma_r_3d(fields.positive_contrast, box_size=1.0, radius=0.2),
            0.2,
            places=4,
        )

    def test_bounded_anticorrelated_contrasts_are_safe_and_exactly_opposite(self) -> None:
        field = gaussian_random_field_3d((8, 8, 8), 1.0, seed=4, target_rms=1.0)

        fields = bounded_anticorrelated_contrasts_3d(field, shape_amplitude=1.0)

        self.assertGreater(float(np.min(fields.positive_contrast)), -1.0)
        self.assertGreater(float(np.min(fields.negative_contrast)), -1.0)
        np.testing.assert_allclose(fields.negative_contrast, -fields.positive_contrast)
        self.assertAlmostEqual(sector_contrast_correlation(fields), -1.0)

    def test_bounded_anticorrelated_contrasts_for_sigma_r_hits_target(self) -> None:
        field = gaussian_random_field_3d((16, 16, 16), 1.0, seed=5, target_rms=1.0)

        fields, _ = bounded_anticorrelated_contrasts_for_sigma_r_3d(
            field,
            box_size=1.0,
            radius=0.2,
            target_sigma=0.05,
            shape_amplitude=1.0,
        )

        self.assertAlmostEqual(
            sigma_r_3d(fields.positive_contrast, box_size=1.0, radius=0.2),
            0.05,
            places=4,
        )

    def test_displacement_from_zero_contrast_is_zero(self) -> None:
        displacement = displacement_from_contrast(np.zeros((4, 4)), 1.0, 0.1)

        np.testing.assert_allclose(displacement, np.zeros((4, 4, 2)))

    def test_displacement_from_zero_contrast_3d_is_zero(self) -> None:
        displacement = displacement_from_contrast_3d(np.zeros((4, 4, 4)), 1.0, 0.1)

        np.testing.assert_allclose(displacement, np.zeros((4, 4, 4, 3)))

    def test_lattice_bodies_from_displacement_places_cell_centers(self) -> None:
        bodies = lattice_bodies_from_displacement(
            np.zeros((2, 2, 2)),
            Sector.POSITIVE,
            box_size=1.0,
        )

        self.assertEqual(len(bodies), 4)
        np.testing.assert_allclose(bodies[0].position, np.asarray([0.25, 0.25]))
        self.assertEqual(bodies[0].sector, Sector.POSITIVE)

    def test_lattice_bodies_from_displacement_3d_places_cell_centers(self) -> None:
        bodies = lattice_bodies_from_displacement_3d(
            np.zeros((2, 2, 2, 3)),
            Sector.POSITIVE,
            box_size=1.0,
        )

        self.assertEqual(len(bodies), 8)
        np.testing.assert_allclose(bodies[0].position, np.asarray([0.25, 0.25, 0.25]))
        self.assertEqual(bodies[0].sector, Sector.POSITIVE)

    def test_two_sector_lattice_initial_conditions_counts_sectors(self) -> None:
        fields = paired_sector_contrasts((4, 4), 1.0, seed=3, target_rms=0.01)

        bodies = two_sector_lattice_initial_conditions(
            fields,
            box_size=1.0,
            displacement_scale=0.001,
        )

        self.assertEqual(len([body for body in bodies if body.sector == Sector.POSITIVE]), 16)
        self.assertEqual(len([body for body in bodies if body.sector == Sector.NEGATIVE]), 16)
        self.assertTrue(all(np.all(body.position >= 0.0) for body in bodies))
        self.assertTrue(all(np.all(body.position < 1.0) for body in bodies))

    def test_two_sector_lattice_initial_conditions_3d_counts_sectors(self) -> None:
        fields = paired_sector_contrasts_3d((4, 4, 4), 1.0, seed=3, target_rms=0.01)

        bodies = two_sector_lattice_initial_conditions_3d(
            fields,
            box_size=1.0,
            displacement_scale=0.001,
        )

        self.assertEqual(len([body for body in bodies if body.sector == Sector.POSITIVE]), 64)
        self.assertEqual(len([body for body in bodies if body.sector == Sector.NEGATIVE]), 64)
        self.assertTrue(all(np.all(body.position >= 0.0) for body in bodies))
        self.assertTrue(all(np.all(body.position < 1.0) for body in bodies))


if __name__ == "__main__":
    unittest.main()
