from __future__ import annotations

import unittest

import numpy as np

from janus_lab.field_statistics import (
    density_contrast,
    density_field_summary,
    normalize_field_to_sigma_r_3d,
    pearson_correlation,
    radial_power_spectrum_2d,
    radial_power_spectrum_3d,
    rms,
    sigma_r_3d,
    signed_sector_contrast,
    spherical_tophat_window,
)


class FieldStatisticsTests(unittest.TestCase):
    def test_density_contrast_normalizes_by_mean(self) -> None:
        contrast = density_contrast(np.asarray([1.0, 3.0]))

        np.testing.assert_allclose(contrast, np.asarray([-0.5, 0.5]))

    def test_pearson_correlation_detects_opposites(self) -> None:
        first = np.asarray([0.0, 1.0, 2.0])
        second = np.asarray([2.0, 1.0, 0.0])

        self.assertAlmostEqual(pearson_correlation(first, second), -1.0)

    def test_signed_sector_contrast_uses_total_density_scale(self) -> None:
        positive = np.asarray([3.0, 1.0])
        negative = np.asarray([1.0, 3.0])

        np.testing.assert_allclose(
            signed_sector_contrast(positive, negative),
            np.asarray([0.5, -0.5]),
        )

    def test_density_field_summary(self) -> None:
        positive = np.asarray([3.0, 1.0])
        negative = np.asarray([1.0, 3.0])

        summary = density_field_summary(positive, negative)

        self.assertAlmostEqual(summary.positive_contrast_rms, 0.5)
        self.assertAlmostEqual(summary.negative_contrast_rms, 0.5)
        self.assertAlmostEqual(summary.sector_correlation, -1.0)
        self.assertAlmostEqual(summary.signed_contrast_rms, 0.5)

    def test_radial_power_spectrum_finds_cosine_mode(self) -> None:
        n = 32
        box_size = 2.0 * np.pi
        x = np.arange(n) * box_size / n
        y = np.arange(n) * box_size / n
        xx, _ = np.meshgrid(x, y, indexing="ij")
        field = np.cos(xx)

        spectrum = radial_power_spectrum_2d(
            field,
            box_size=box_size,
            bin_edges=np.asarray([0.5, 1.5, 2.5]),
        )

        self.assertAlmostEqual(rms(field), np.sqrt(0.5))
        self.assertGreater(spectrum.power[0], 0.49)
        self.assertLess(spectrum.power[1], 1e-24)

    def test_radial_power_spectrum_3d_finds_cosine_mode(self) -> None:
        n = 16
        box_size = 2.0 * np.pi
        x = np.arange(n) * box_size / n
        y = np.arange(n) * box_size / n
        z = np.arange(n) * box_size / n
        xx, _, _ = np.meshgrid(x, y, z, indexing="ij")
        field = np.cos(xx)

        spectrum = radial_power_spectrum_3d(
            field,
            box_size=box_size,
            bin_edges=np.asarray([0.5, 1.5, 2.5]),
        )

        self.assertAlmostEqual(rms(field), np.sqrt(0.5))
        self.assertGreater(spectrum.power[0], 0.49)
        self.assertLess(spectrum.power[1], 1e-24)

    def test_spherical_tophat_window_is_one_at_zero(self) -> None:
        window = spherical_tophat_window(np.asarray([0.0, 1e-10]))

        np.testing.assert_allclose(window, np.asarray([1.0, 1.0]))

    def test_sigma_r_3d_zero_for_constant_field(self) -> None:
        self.assertEqual(sigma_r_3d(np.ones((8, 8, 8)), box_size=1.0, radius=0.1), 0.0)

    def test_normalize_field_to_sigma_r_3d_hits_target(self) -> None:
        n = 16
        box_size = 1.0
        x = np.arange(n) * box_size / n
        y = np.arange(n) * box_size / n
        z = np.arange(n) * box_size / n
        xx, _, _ = np.meshgrid(x, y, z, indexing="ij")
        field = np.cos(2.0 * np.pi * xx / box_size)

        normalized = normalize_field_to_sigma_r_3d(
            field,
            box_size=box_size,
            radius=0.2,
            target_sigma=0.3,
        )

        self.assertAlmostEqual(sigma_r_3d(normalized, box_size=box_size, radius=0.2), 0.3)


if __name__ == "__main__":
    unittest.main()
