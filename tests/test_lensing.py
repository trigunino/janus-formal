from __future__ import annotations

import unittest

import numpy as np

from janus_lab.lensing import (
    cross_sector_optical_projection_factor,
    equal_comoving_cross_projection_factor,
    flrw_metric_determinant_ratio_factor,
    janus_absolute_lensing_coefficients,
    janus_tensor_lensing_prefactor,
    janus_open_angular_diameter_distance_between_mpc,
    janus_open_angular_diameter_distance_mpc,
    janus_open_angular_lensing_distance_kernel_mpc,
    janus_open_comoving_lensing_distance_kernel_mpc,
    janus_curvature_radius_mpc,
    janus_open_chi,
    janus_open_lensing_geometry_kernel,
    janus_open_marker_distance,
    janus_open_transverse_distance_mpc,
    janus_source_distribution_lensing_kernel,
    janus_source_distribution_lensing_weights,
    janus_tomographic_lensing_weights,
    boosted_perfect_fluid_t00_source,
    beta_field_is_prediction_ready,
    lorentz_gamma_from_beta_vectors,
    negative_mass_sphere_annular_dimming_map,
    negative_mass_sphere_annular_dimming_profile,
    negative_mass_sphere_reduced_deflection_profile,
    negative_sector_lensing_weight_factor,
    positive_photon_convergence_proxy_2d,
    positive_effective_negative_density,
    positive_photon_lensing_contrast_with_density_convention,
    positive_photon_lensing_contrast_with_determinant_ratio,
    positive_photon_lensing_contrast,
    positive_photon_lensing_potential_2d,
    positive_photon_lensing_potential_3d,
    positive_photon_lensing_sigma_r_3d,
    positive_photon_lensing_source_grid,
    positive_photon_lensing_source_grid_with_density_convention,
    positive_photon_lensing_source_grid_with_determinant_ratio,
    positive_photon_weak_field_weyl_components_2d,
    positive_noncomoving_t00_source_grid,
    positive_flrw_photon_energy_factor,
    positive_flrw_jacobi_reduced_projection_factor,
    positive_flrw_ricci_projection_factor,
    relative_velocity_cross_projection_factor,
    relative_velocity_cross_projection_from_vectors,
    relative_velocity_cross_projection_from_velocities_km_s,
    transported_four_velocity_from_beta_vectors,
    project_lensing_contrast_2d,
    project_lensing_contrast_2d_with_coefficients,
    shear_from_convergence_proxy_2d,
    shear_proxy_rms,
    standard_dust_lensing_projection_factor,
    standard_weak_lensing_prefactor,
    validate_lensing_factor_provenance,
    validate_beta_field_provenance,
    velocity_km_s_to_beta_vectors,
    weak_field_weyl_screen_tidal_components_2d,
)
from janus_lab.models import JanusExpansion
from janus_lab.poisson import (
    effective_density_grid,
    solve_periodic_poisson_2d,
    solve_periodic_poisson_3d,
)
from janus_lab.signed_sector import Sector


class LensingTests(unittest.TestCase):
    def test_positive_photon_source_is_centered_signed_density(self) -> None:
        positive = np.asarray([3.0, 1.0])
        negative = np.asarray([1.0, 1.0])

        source = positive_photon_lensing_source_grid(positive, negative)

        np.testing.assert_allclose(source, np.asarray([1.0, -1.0]))

    def test_flrw_determinant_ratio_is_fourth_power_scale_ratio(self) -> None:
        ratio = flrw_metric_determinant_ratio_factor(
            np.asarray([1.0, 2.0]),
            np.asarray([1.0, 1.0]),
        )

        np.testing.assert_allclose(ratio, np.asarray([1.0, 1.0 / 16.0]))

    def test_determinant_weighted_source_changes_negative_sector_weight(self) -> None:
        positive = np.asarray([3.0, 1.0])
        negative = np.asarray([1.0, 1.0])

        source = positive_photon_lensing_source_grid_with_determinant_ratio(
            positive,
            negative,
            determinant_ratio=2.0,
            subtract_mean=False,
        )

        np.testing.assert_allclose(source, np.asarray([1.0, -1.0]))

    def test_determinant_weighted_contrast_reduces_to_current_source_at_one(self) -> None:
        positive = np.asarray([3.0, 1.0])
        negative = np.asarray([1.0, 1.0])

        current = positive_photon_lensing_contrast(positive, negative)
        weighted = positive_photon_lensing_contrast_with_determinant_ratio(
            positive,
            negative,
            determinant_ratio=1.0,
        )

        np.testing.assert_allclose(weighted, current)

    def test_cross_projection_factor_is_projection_ratio(self) -> None:
        factor = cross_sector_optical_projection_factor(
            np.asarray([2.0, 4.0]),
            np.asarray([1.0, 8.0]),
        )

        np.testing.assert_allclose(factor, np.asarray([0.5, 2.0]))

    def test_equal_comoving_cross_projection_factor_is_unity(self) -> None:
        factor = equal_comoving_cross_projection_factor(np.asarray([0.0, 0.5, 2.0]))

        np.testing.assert_allclose(factor, np.ones(3))

    def test_relative_velocity_cross_projection_comoving_is_unity(self) -> None:
        factor = relative_velocity_cross_projection_factor(0.0, 0.0)

        self.assertAlmostEqual(factor, 1.0)

    def test_relative_velocity_cross_projection_parallel_motion(self) -> None:
        beta = 0.5
        toward = relative_velocity_cross_projection_factor(beta, beta)
        away = relative_velocity_cross_projection_factor(beta, -beta)

        self.assertAlmostEqual(toward, (1.0 - beta) / (1.0 + beta))
        self.assertAlmostEqual(away, (1.0 + beta) / (1.0 - beta))

    def test_relative_velocity_cross_projection_rejects_invalid_beta(self) -> None:
        with self.assertRaises(ValueError):
            relative_velocity_cross_projection_factor(1.0, 0.0)
        with self.assertRaises(ValueError):
            relative_velocity_cross_projection_factor(0.2, 0.3)

    def test_relative_velocity_cross_projection_from_vectors(self) -> None:
        beta_vectors = np.asarray(
            [
                [0.5, 0.0, 0.0],
                [-0.5, 0.0, 0.0],
                [0.0, 0.5, 0.0],
            ]
        )
        factors = relative_velocity_cross_projection_from_vectors(
            beta_vectors,
            photon_direction=np.asarray([1.0, 0.0, 0.0]),
        )

        np.testing.assert_allclose(
            factors,
            np.asarray([1.0 / 3.0, 3.0, 4.0 / 3.0]),
        )

    def test_relative_velocity_cross_projection_from_vectors_rejects_bad_direction(self) -> None:
        with self.assertRaises(ValueError):
            relative_velocity_cross_projection_from_vectors(
                np.asarray([[0.0, 0.0]]),
                np.asarray([0.0, 0.0]),
            )
        with self.assertRaises(ValueError):
            relative_velocity_cross_projection_from_vectors(
                np.asarray([[0.0, 0.0]]),
                np.asarray([1.0, 0.0, 0.0]),
            )

    def test_velocity_km_s_to_beta_vectors(self) -> None:
        beta = velocity_km_s_to_beta_vectors(
            np.asarray([[149896.229, 0.0, 0.0]]),
            speed_of_light_km_s=299792.458,
        )

        np.testing.assert_allclose(beta, np.asarray([[0.5, 0.0, 0.0]]))

    def test_velocity_km_s_to_beta_vectors_rejects_superluminal_norm(self) -> None:
        with self.assertRaises(ValueError):
            velocity_km_s_to_beta_vectors(
                np.asarray([[300000.0, 300000.0, 0.0]]),
                speed_of_light_km_s=299792.458,
            )

    def test_cross_projection_from_velocities_km_s(self) -> None:
        q_cross = relative_velocity_cross_projection_from_velocities_km_s(
            np.asarray([[149896.229, 0.0, 0.0]]),
            photon_direction=np.asarray([1.0, 0.0, 0.0]),
            speed_of_light_km_s=299792.458,
        )

        np.testing.assert_allclose(q_cross, np.asarray([1.0 / 3.0]))

    def test_lorentz_gamma_and_transported_four_velocity_from_beta_vectors(self) -> None:
        beta = np.asarray([[0.0, 0.0], [0.6, 0.0]])

        gamma = lorentz_gamma_from_beta_vectors(beta)
        four_velocity = transported_four_velocity_from_beta_vectors(beta)

        np.testing.assert_allclose(gamma, np.asarray([1.0, 1.25]))
        np.testing.assert_allclose(
            four_velocity,
            np.asarray([[1.0, 0.0, 0.0], [1.25, 0.75, 0.0]]),
        )

    def test_lorentz_gamma_rejects_superluminal_beta_vectors(self) -> None:
        with self.assertRaises(ValueError):
            lorentz_gamma_from_beta_vectors(np.asarray([[1.0, 0.0]]))

    def test_boosted_perfect_fluid_t00_source_includes_pressure_and_pi(self) -> None:
        value = boosted_perfect_fluid_t00_source(
            np.asarray([2.0]),
            np.asarray([[0.6, 0.0]]),
            pressure_abs=np.asarray([0.5]),
            pi00=np.asarray([0.25]),
        )

        np.testing.assert_allclose(value, np.asarray([(2.0 + 0.5) * 1.25**2 - 0.5 + 0.25]))

    def test_positive_noncomoving_t00_source_grid_reduces_to_comoving_source_at_zero_beta(self) -> None:
        positive = np.asarray([3.0, 1.0])
        negative = np.asarray([1.0, 1.0])
        beta = np.zeros((2, 2))

        source = positive_noncomoving_t00_source_grid(positive, negative, beta, subtract_mean=False)

        np.testing.assert_allclose(source, np.asarray([2.0, 0.0]))

    def test_beta_field_provenance_distinguishes_diagnostic_and_prediction_ready(self) -> None:
        self.assertEqual(
            validate_beta_field_provenance("pm_hubble_calibrated_diagnostic"),
            "pm_hubble_calibrated_diagnostic",
        )
        self.assertFalse(beta_field_is_prediction_ready("pm_hubble_calibrated_diagnostic"))
        self.assertTrue(beta_field_is_prediction_ready("source_derived_janus_dynamics"))

    def test_beta_field_provenance_rejects_fitted_lensing_labels(self) -> None:
        with self.assertRaises(ValueError):
            validate_beta_field_provenance("sigma8_fit")
        with self.assertRaises(ValueError):
            positive_noncomoving_t00_source_grid(
                np.ones(2),
                np.ones(2),
                np.zeros((2, 2)),
                beta_field_provenance="shear_fit",
            )

    def test_negative_sector_lensing_weight_uses_effective_density_convention(self) -> None:
        weight = negative_sector_lensing_weight_factor(
            negative_density_convention="positive_effective",
            determinant_ratio=10.0,
            cross_projection_ratio=2.0,
        )

        self.assertAlmostEqual(weight, 2.0)

    def test_negative_sector_lensing_weight_uses_proper_density_convention(self) -> None:
        weight = negative_sector_lensing_weight_factor(
            negative_density_convention="negative_proper",
            determinant_ratio=10.0,
            cross_projection_ratio=2.0,
        )

        self.assertAlmostEqual(weight, 20.0)

    def test_raw_scale_ratio_provenance_is_rejected_as_lensing_amplitude(self) -> None:
        for provenance in (
            "raw_flrw_scale_ratio",
            "det4_metric_plus",
            "weight3_dust_plus",
        ):
            with self.assertRaises(ValueError):
                validate_lensing_factor_provenance(provenance)

        self.assertEqual(
            validate_lensing_factor_provenance("negative_proper_density_volume"),
            "negative_proper_density_volume",
        )

    def test_negative_sector_weight_rejects_det4_metric_as_amplitude(self) -> None:
        with self.assertRaises(ValueError):
            negative_sector_lensing_weight_factor(
                negative_density_convention="negative_proper",
                determinant_ratio=0.5,
                cross_projection_ratio=1.0,
                determinant_ratio_provenance="det4_metric_plus",
            )

    def test_tensor_prefactor_rejects_weight3_dust_as_amplitude(self) -> None:
        with self.assertRaises(ValueError):
            janus_tensor_lensing_prefactor(
                70.0,
                0.315,
                determinant_ratio=0.5,
                determinant_ratio_provenance="weight3_dust_plus",
            )

    def test_positive_effective_negative_density_absorbs_determinant_ratio(self) -> None:
        proper = np.asarray([1.0, 2.0])
        effective = positive_effective_negative_density(
            proper,
            determinant_ratio=np.asarray([2.0, 3.0]),
        )

        np.testing.assert_allclose(effective, np.asarray([2.0, 6.0]))

    def test_effective_density_source_matches_proper_density_with_determinant(self) -> None:
        positive = np.asarray([3.0, 1.0])
        proper_negative = np.asarray([1.0, 1.0])
        determinant = 2.0
        effective_negative = positive_effective_negative_density(
            proper_negative,
            determinant_ratio=determinant,
        )

        from_proper = positive_photon_lensing_source_grid_with_density_convention(
            positive,
            proper_negative,
            negative_density_convention="negative_proper",
            determinant_ratio=determinant,
            subtract_mean=False,
        )
        from_effective = positive_photon_lensing_source_grid_with_density_convention(
            positive,
            effective_negative,
            negative_density_convention="positive_effective",
            subtract_mean=False,
        )

        np.testing.assert_allclose(from_effective, from_proper)

    def test_raw_flrw_weight_stack_is_sixth_power_scale_ratio(self) -> None:
        scale_ratio = 0.5
        determinant = scale_ratio**4
        cross = scale_ratio**2

        weight = negative_sector_lensing_weight_factor(
            negative_density_convention="negative_proper",
            determinant_ratio=determinant,
            cross_projection_ratio=cross,
        )

        self.assertAlmostEqual(weight, scale_ratio**6)

    def test_density_convention_effective_ignores_determinant_ratio(self) -> None:
        positive = np.asarray([3.0, 1.0])
        negative = np.asarray([1.0, 1.0])

        source = positive_photon_lensing_source_grid_with_density_convention(
            positive,
            negative,
            negative_density_convention="positive_effective",
            determinant_ratio=2.0,
            subtract_mean=False,
        )

        np.testing.assert_allclose(source, np.asarray([2.0, 0.0]))

    def test_density_convention_effective_applies_cross_projection_ratio(self) -> None:
        positive = np.asarray([3.0, 1.0])
        negative = np.asarray([1.0, 1.0])

        source = positive_photon_lensing_source_grid_with_density_convention(
            positive,
            negative,
            negative_density_convention="positive_effective",
            cross_projection_ratio=2.0,
            subtract_mean=False,
        )

        np.testing.assert_allclose(source, np.asarray([1.0, -1.0]))

    def test_density_convention_negative_proper_applies_determinant_ratio(self) -> None:
        positive = np.asarray([3.0, 1.0])
        negative = np.asarray([1.0, 1.0])

        source = positive_photon_lensing_source_grid_with_density_convention(
            positive,
            negative,
            negative_density_convention="negative_proper",
            determinant_ratio=2.0,
            subtract_mean=False,
        )

        np.testing.assert_allclose(source, np.asarray([1.0, -1.0]))

    def test_density_convention_negative_proper_applies_cross_projection_ratio(self) -> None:
        positive = np.asarray([3.0, 1.0])
        negative = np.asarray([1.0, 1.0])

        source = positive_photon_lensing_source_grid_with_density_convention(
            positive,
            negative,
            negative_density_convention="negative_proper",
            determinant_ratio=2.0,
            cross_projection_ratio=0.5,
            subtract_mean=False,
        )

        np.testing.assert_allclose(source, np.asarray([2.0, 0.0]))

    def test_density_convention_contrast_default_matches_current_source(self) -> None:
        positive = np.asarray([3.0, 1.0])
        negative = np.asarray([1.0, 1.0])

        current = positive_photon_lensing_contrast(positive, negative)
        convention = positive_photon_lensing_contrast_with_density_convention(
            positive,
            negative,
        )

        np.testing.assert_allclose(convention, current)

    def test_density_convention_rejects_unknown_mode(self) -> None:
        with self.assertRaises(ValueError):
            positive_photon_lensing_source_grid_with_density_convention(
                np.asarray([1.0]),
                np.asarray([1.0]),
                negative_density_convention="raw",
            )

    def test_negative_mass_hole_has_positive_lensing_source(self) -> None:
        positive = np.asarray([1.0, 1.0])
        negative = np.asarray([0.0, 2.0])

        contrast = positive_photon_lensing_contrast(positive, negative)

        np.testing.assert_allclose(contrast, np.asarray([0.5, -0.5]))

    def test_negative_mass_cluster_has_negative_lensing_source(self) -> None:
        positive = np.asarray([1.0, 1.0])
        negative = np.asarray([2.0, 0.0])

        contrast = positive_photon_lensing_contrast(positive, negative)

        np.testing.assert_allclose(contrast, np.asarray([-0.5, 0.5]))

    def test_potential_2d_matches_positive_metric_poisson(self) -> None:
        positive = np.zeros((16, 16))
        negative = np.zeros((16, 16))
        positive[4, 4] = 1.0
        negative[10, 10] = 0.5

        expected = solve_periodic_poisson_2d(
            effective_density_grid(positive, negative, Sector.POSITIVE),
            box_size=1.0,
        )
        actual = positive_photon_lensing_potential_2d(positive, negative, box_size=1.0)

        np.testing.assert_allclose(actual, expected)

    def test_potential_3d_matches_positive_metric_poisson(self) -> None:
        positive = np.zeros((8, 8, 8))
        negative = np.zeros((8, 8, 8))
        positive[2, 2, 2] = 1.0
        negative[5, 5, 5] = 0.5

        expected = solve_periodic_poisson_3d(
            effective_density_grid(positive, negative, Sector.POSITIVE),
            box_size=1.0,
        )
        actual = positive_photon_lensing_potential_3d(positive, negative, box_size=1.0)

        np.testing.assert_allclose(actual, expected)

    def test_lensing_sigma_r_matches_exact_anticorrelation(self) -> None:
        n = 16
        box_size = 1.0
        radius = 0.2
        x = np.arange(n) * box_size / n
        xx, _, _ = np.meshgrid(x, x, x, indexing="ij")
        delta = 0.1 * np.cos(2.0 * np.pi * xx / box_size)

        sigma = positive_photon_lensing_sigma_r_3d(
            1.0 + delta,
            1.0 - delta,
            box_size=box_size,
            radius=radius,
        )

        self.assertGreater(sigma, 0.0)

    def test_rejects_negative_absolute_density(self) -> None:
        with self.assertRaises(ValueError):
            positive_photon_lensing_contrast(np.asarray([1.0]), np.asarray([-1.0]))

    def test_projection_defaults_to_axis_mean(self) -> None:
        field = np.arange(24, dtype=float).reshape(2, 3, 4)

        projected = project_lensing_contrast_2d(field, axis=2)

        np.testing.assert_allclose(projected, np.mean(field, axis=2))

    def test_projection_uses_normalized_weights(self) -> None:
        field = np.asarray([[[1.0, 3.0]], [[5.0, 7.0]]])

        projected = project_lensing_contrast_2d(field, axis=2, weights=np.asarray([1.0, 3.0]))

        np.testing.assert_allclose(projected, np.asarray([[2.5], [6.5]]))

    def test_positive_convergence_proxy_projects_lensing_contrast(self) -> None:
        delta = np.asarray(
            [
                [[0.1, 0.3], [0.2, 0.4]],
                [[-0.1, -0.3], [-0.2, -0.4]],
            ]
        )

        projected = positive_photon_convergence_proxy_2d(1.0 + delta, 1.0 - delta)

        np.testing.assert_allclose(projected, np.mean(delta, axis=2))

    def test_negative_mass_sphere_deflection_is_annular(self) -> None:
        impact = np.asarray([0.0, 0.5, 1.0, 2.0])

        deflection = negative_mass_sphere_reduced_deflection_profile(
            impact,
            sphere_radius=1.0,
        )
        dimming = negative_mass_sphere_annular_dimming_profile(
            impact,
            sphere_radius=1.0,
        )

        np.testing.assert_allclose(deflection, np.asarray([-0.0, -0.25, -1.0, -0.5]))
        np.testing.assert_allclose(dimming, np.asarray([0.0, 0.25, 1.0, 0.5]))

    def test_negative_mass_sphere_profile_rejects_bad_inputs(self) -> None:
        with self.assertRaises(ValueError):
            negative_mass_sphere_reduced_deflection_profile(np.asarray([0.0]), 0.0)
        with self.assertRaises(ValueError):
            negative_mass_sphere_reduced_deflection_profile(np.asarray([-1.0]), 1.0)
        with self.assertRaises(ValueError):
            negative_mass_sphere_reduced_deflection_profile(np.asarray([1.0]), 1.0, -1.0)

    def test_negative_mass_sphere_dimming_map_uses_radius_from_center(self) -> None:
        coordinates = np.asarray([-1.0, 0.0, 1.0])
        xx, yy = np.meshgrid(coordinates, coordinates, indexing="ij")

        dimming = negative_mass_sphere_annular_dimming_map(
            xx,
            yy,
            sphere_radius=1.0,
        )

        self.assertAlmostEqual(dimming[1, 1], 0.0)
        self.assertAlmostEqual(dimming[0, 1], 1.0)
        self.assertAlmostEqual(dimming[1, 0], 1.0)
        self.assertLess(dimming[0, 0], 1.0)

    def test_negative_mass_sphere_dimming_map_rejects_shape_mismatch(self) -> None:
        with self.assertRaises(ValueError):
            negative_mass_sphere_annular_dimming_map(
                np.zeros((2, 2)),
                np.zeros((2, 3)),
                sphere_radius=1.0,
            )

    def test_projection_rejects_bad_weights(self) -> None:
        with self.assertRaises(ValueError):
            project_lensing_contrast_2d(np.ones((2, 2, 2)), weights=np.asarray([0.0, 0.0]))

    def test_weak_field_weyl_tidal_operator_zeroes_constant_potential(self) -> None:
        components = weak_field_weyl_screen_tidal_components_2d(np.ones((8, 8)), box_size=1.0)

        np.testing.assert_allclose(components["convergence"], np.zeros((8, 8)), atol=1e-12)
        np.testing.assert_allclose(components["gamma1"], np.zeros((8, 8)), atol=1e-12)
        np.testing.assert_allclose(components["gamma2"], np.zeros((8, 8)), atol=1e-12)

    def test_weak_field_weyl_tidal_operator_separates_trace_and_trace_free_parts(self) -> None:
        n = 16
        box_size = 1.0
        x = np.arange(n, dtype=float) / n
        xx, _ = np.meshgrid(x, x, indexing="ij")
        potential = np.cos(2.0 * np.pi * xx)
        components = weak_field_weyl_screen_tidal_components_2d(potential, box_size=box_size)
        expected = -0.5 * (2.0 * np.pi) ** 2 * potential

        np.testing.assert_allclose(components["convergence"], expected, atol=1e-10)
        np.testing.assert_allclose(components["gamma1"], expected, atol=1e-10)
        np.testing.assert_allclose(components["gamma2"], np.zeros_like(potential), atol=1e-10)

    def test_weak_field_weyl_tidal_operator_rejects_bad_inputs(self) -> None:
        with self.assertRaises(ValueError):
            weak_field_weyl_screen_tidal_components_2d(np.ones(4), box_size=1.0)
        with self.assertRaises(ValueError):
            weak_field_weyl_screen_tidal_components_2d(np.ones((4, 4)), box_size=0.0)

    def test_positive_photon_weak_field_weyl_chain_matches_declared_potential_operator(self) -> None:
        positive = np.ones((8, 8))
        negative = np.zeros((8, 8))
        positive[2, 2] = 2.0
        chain = positive_photon_weak_field_weyl_components_2d(
            positive,
            negative,
            box_size=1.0,
            source_provenance="source_derived",
        )
        direct = weak_field_weyl_screen_tidal_components_2d(
            chain["potential"],
            box_size=1.0,
        )

        np.testing.assert_allclose(chain["gamma1"], direct["gamma1"])
        np.testing.assert_allclose(chain["gamma2"], direct["gamma2"])
        self.assertEqual(chain["source_provenance"], "source_derived")
        self.assertFalse(chain["restricted_metric_ready"])
        self.assertFalse(chain["prediction_ready"])

    def test_positive_photon_weak_field_weyl_chain_can_mark_restricted_metric_branch(self) -> None:
        chain = positive_photon_weak_field_weyl_components_2d(
            np.ones((8, 8)),
            np.zeros((8, 8)),
            box_size=1.0,
            source_provenance="source_derived",
            restricted_metric_closure=True,
        )

        self.assertTrue(chain["restricted_metric_ready"])
        self.assertFalse(chain["prediction_ready"])

    def test_positive_photon_weak_field_weyl_chain_rejects_fit_provenance(self) -> None:
        with self.assertRaises(ValueError):
            positive_photon_weak_field_weyl_components_2d(
                np.ones((4, 4)),
                np.zeros((4, 4)),
                box_size=1.0,
                source_provenance="shear_fit",
            )

    def test_janus_open_marker_distance_starts_at_zero(self) -> None:
        model = JanusExpansion.from_q0(-0.087)

        self.assertAlmostEqual(janus_open_marker_distance(0.0, model), 0.0)
        self.assertAlmostEqual(janus_open_chi(0.0, model), 0.0)
        self.assertGreater(janus_open_marker_distance(1.0, model), 0.0)

    def test_janus_transverse_distance_has_physical_scale(self) -> None:
        model = JanusExpansion.from_q0(-0.087)

        radius = janus_curvature_radius_mpc(model, h0_km_s_mpc=70.0)
        distance = janus_open_transverse_distance_mpc(1.0, model, h0_km_s_mpc=70.0)

        self.assertGreater(radius, 0.0)
        self.assertGreater(distance, 0.0)

    def test_janus_angular_diameter_distance_is_transverse_over_one_plus_z(self) -> None:
        model = JanusExpansion.from_q0(-0.087)
        z = np.asarray([0.5, 1.0])

        transverse = janus_open_transverse_distance_mpc(z, model, h0_km_s_mpc=70.0)
        angular = janus_open_angular_diameter_distance_mpc(z, model, h0_km_s_mpc=70.0)

        np.testing.assert_allclose(angular, transverse / (1.0 + z))

    def test_janus_lens_source_angular_distance_zeroes_beyond_source(self) -> None:
        model = JanusExpansion.from_q0(-0.087)
        distance = janus_open_angular_diameter_distance_between_mpc(
            np.asarray([0.5, 2.0, 2.5]),
            2.0,
            model,
            h0_km_s_mpc=70.0,
        )

        self.assertGreater(distance[0], 0.0)
        self.assertAlmostEqual(distance[1], 0.0)
        self.assertAlmostEqual(distance[2], 0.0)

    def test_janus_angular_kernel_matches_comoving_kernel_times_scale_factor(self) -> None:
        model = JanusExpansion.from_q0(-0.087)
        z = np.asarray([0.5, 1.0])

        comoving = janus_open_comoving_lensing_distance_kernel_mpc(
            z,
            2.0,
            model,
            h0_km_s_mpc=70.0,
        )
        angular = janus_open_angular_lensing_distance_kernel_mpc(
            z,
            2.0,
            model,
            h0_km_s_mpc=70.0,
        )

        np.testing.assert_allclose(angular, comoving / (1.0 + z))

    def test_janus_lensing_kernel_is_geometric_window(self) -> None:
        model = JanusExpansion.from_q0(-0.087)
        z = np.asarray([0.0, 0.5, 1.0, 2.0])

        kernel = janus_open_lensing_geometry_kernel(z, z_source=2.0, model=model)

        self.assertAlmostEqual(kernel[0], 0.0)
        self.assertGreater(kernel[1], 0.0)
        self.assertGreater(kernel[2], 0.0)
        self.assertAlmostEqual(kernel[3], 0.0)

    def test_janus_tomographic_weights_normalize(self) -> None:
        model = JanusExpansion.from_q0(-0.087)
        weights = janus_tomographic_lensing_weights(
            np.linspace(0.0, 2.0, 16),
            z_source=2.0,
            model=model,
        )

        self.assertAlmostEqual(float(np.sum(weights)), 1.0)
        self.assertTrue(np.all(weights >= 0.0))

    def test_source_distribution_single_source_matches_delta_source(self) -> None:
        model = JanusExpansion.from_q0(-0.087)
        z_slices = np.linspace(0.0, 2.0, 16)

        direct = janus_tomographic_lensing_weights(z_slices, z_source=2.0, model=model)
        distributed = janus_source_distribution_lensing_weights(
            z_slices,
            np.asarray([2.0]),
            np.asarray([1.0]),
            model,
        )

        np.testing.assert_allclose(distributed, direct)

    def test_source_distribution_kernel_combines_sources(self) -> None:
        model = JanusExpansion.from_q0(-0.087)
        z_lens = np.asarray([0.5, 1.5])

        kernel = janus_source_distribution_lensing_kernel(
            z_lens,
            np.asarray([1.0, 2.0]),
            np.asarray([1.0, 1.0]),
            model,
        )

        self.assertGreater(kernel[0], kernel[1])
        self.assertGreater(kernel[1], 0.0)

    def test_source_distribution_rejects_bad_weights(self) -> None:
        model = JanusExpansion.from_q0(-0.087)
        with self.assertRaises(ValueError):
            janus_source_distribution_lensing_weights(
                np.linspace(0.0, 1.0, 8),
                np.asarray([1.0]),
                np.asarray([0.0]),
                model,
            )

    def test_absolute_lensing_coefficients_are_dimensionless_positive_window(self) -> None:
        model = JanusExpansion.from_q0(-0.087)
        coefficients = janus_absolute_lensing_coefficients(
            np.linspace(0.0, 2.0, 16),
            np.asarray([2.0]),
            np.asarray([1.0]),
            model,
            h0_km_s_mpc=70.0,
            omega_abs=0.315,
        )

        self.assertEqual(coefficients.shape, (16,))
        self.assertAlmostEqual(coefficients[0], 0.0)
        self.assertAlmostEqual(coefficients[-1], 0.0)
        self.assertGreater(float(np.max(coefficients)), 0.0)

    def test_standard_prefactor_is_explicit_scaffold(self) -> None:
        prefactor = standard_weak_lensing_prefactor(70.0, 0.315)

        self.assertAlmostEqual(prefactor, 1.5 * 0.315 * (70.0 / 299792.458) ** 2)

    def test_tensor_lensing_prefactor_factorizes_without_fit(self) -> None:
        base = standard_weak_lensing_prefactor(70.0, 0.315)
        prefactor = janus_tensor_lensing_prefactor(
            70.0,
            0.315,
            source_factor=2.0,
            determinant_ratio=3.0,
            cross_projection_ratio=5.0,
            projection_factor=7.0,
            distance_factor=11.0,
        )

        self.assertAlmostEqual(prefactor, base * 2.0 * 3.0 * 5.0 * 7.0 * 11.0)

    def test_standard_projection_factor_is_explicit_scaffold(self) -> None:
        factor = standard_dust_lensing_projection_factor(np.asarray([0.0, 0.5, 2.0]))

        np.testing.assert_allclose(factor, np.asarray([1.0, 1.5, 3.0]))

    def test_positive_flrw_null_geodesic_energy_scaling(self) -> None:
        factor = positive_flrw_photon_energy_factor(np.asarray([0.0, 0.5, 2.0]))

        np.testing.assert_allclose(factor, np.asarray([1.0, 1.5, 3.0]))

    def test_positive_flrw_ricci_projection_is_energy_squared(self) -> None:
        factor = positive_flrw_ricci_projection_factor(np.asarray([0.0, 0.5, 2.0]))

        np.testing.assert_allclose(factor, np.asarray([1.0, 2.25, 9.0]))

    def test_positive_flrw_jacobi_reduction_returns_convergence_factor(self) -> None:
        factor = positive_flrw_jacobi_reduced_projection_factor(np.asarray([0.0, 0.5, 2.0]))

        np.testing.assert_allclose(factor, np.asarray([1.0, 1.5, 3.0]))

    def test_projection_with_coefficients_does_not_normalize(self) -> None:
        field = np.ones((2, 1, 3))
        coefficients = np.asarray([1.0, 2.0, 3.0])

        projected = project_lensing_contrast_2d_with_coefficients(
            field,
            coefficients,
            axis=2,
        )

        np.testing.assert_allclose(projected, np.full((2, 1), 6.0))

    def test_shear_from_convergence_recovers_x_mode(self) -> None:
        n = 32
        box_size = 2.0 * np.pi
        x = np.arange(n) * box_size / n
        xx, _ = np.meshgrid(x, x, indexing="ij")
        kappa = np.cos(xx)

        gamma1, gamma2 = shear_from_convergence_proxy_2d(kappa, box_size=box_size)

        np.testing.assert_allclose(gamma1, kappa, atol=1e-12)
        np.testing.assert_allclose(gamma2, np.zeros_like(kappa), atol=1e-12)

    def test_shear_from_convergence_zeroes_constant_mode(self) -> None:
        gamma1, gamma2 = shear_from_convergence_proxy_2d(np.ones((8, 8)), box_size=1.0)

        np.testing.assert_allclose(gamma1, np.zeros((8, 8)))
        np.testing.assert_allclose(gamma2, np.zeros((8, 8)))

    def test_shear_rms_combines_components(self) -> None:
        gamma1 = np.asarray([3.0, 0.0])
        gamma2 = np.asarray([0.0, 4.0])

        self.assertAlmostEqual(shear_proxy_rms(gamma1, gamma2), np.sqrt(12.5))


if __name__ == "__main__":
    unittest.main()
