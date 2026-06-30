from __future__ import annotations

import unittest

import numpy as np

from janus_lab.signed_sector import (
    BodyState,
    NewtonianInteraction,
    PointSource,
    Sector,
    accelerations_for_bodies,
    density_sign,
    interaction_sign,
    janus_interaction,
    kinetic_energy,
    leapfrog_step,
    metric_sheet_for,
    metric_equation_sign,
    newtonian_coupling_matrix,
    newtonian_coupling_sign,
    pair_potential_energy,
    poisson_rhs_density,
    point_source_acceleration,
    point_source_potential,
    total_acceleration,
    total_energy,
)


class SignedSectorTests(unittest.TestCase):
    def test_metric_sheet_tracks_sector(self) -> None:
        self.assertEqual(metric_sheet_for(Sector.POSITIVE), "g_plus")
        self.assertEqual(metric_sheet_for(Sector.NEGATIVE), "g_minus")

    def test_same_sectors_attract_opposite_sectors_repel(self) -> None:
        self.assertEqual(
            janus_interaction(Sector.POSITIVE, Sector.POSITIVE),
            NewtonianInteraction.ATTRACT,
        )
        self.assertEqual(
            janus_interaction(Sector.NEGATIVE, Sector.NEGATIVE),
            NewtonianInteraction.ATTRACT,
        )
        self.assertEqual(
            janus_interaction(Sector.POSITIVE, Sector.NEGATIVE),
            NewtonianInteraction.REPEL,
        )
        self.assertEqual(
            janus_interaction(Sector.NEGATIVE, Sector.POSITIVE),
            NewtonianInteraction.REPEL,
        )

    def test_interaction_sign(self) -> None:
        self.assertEqual(interaction_sign(Sector.POSITIVE, Sector.POSITIVE), 1.0)
        self.assertEqual(interaction_sign(Sector.NEGATIVE, Sector.POSITIVE), -1.0)

    def test_coupling_sign_follows_density_and_metric_equation_signs(self) -> None:
        self.assertEqual(density_sign(Sector.POSITIVE), 1.0)
        self.assertEqual(density_sign(Sector.NEGATIVE), -1.0)
        self.assertEqual(metric_equation_sign(Sector.POSITIVE), 1.0)
        self.assertEqual(metric_equation_sign(Sector.NEGATIVE), -1.0)
        self.assertEqual(newtonian_coupling_sign(Sector.POSITIVE, Sector.POSITIVE), 1.0)
        self.assertEqual(newtonian_coupling_sign(Sector.NEGATIVE, Sector.NEGATIVE), 1.0)
        self.assertEqual(newtonian_coupling_sign(Sector.POSITIVE, Sector.NEGATIVE), -1.0)
        self.assertEqual(newtonian_coupling_sign(Sector.NEGATIVE, Sector.POSITIVE), -1.0)

    def test_coupling_matrix_rows_are_test_metrics(self) -> None:
        expected = np.asarray([[1.0, -1.0], [-1.0, 1.0]])

        np.testing.assert_allclose(newtonian_coupling_matrix(), expected)

    def test_poisson_rhs_uses_four_pi_g_normalization(self) -> None:
        self.assertAlmostEqual(
            poisson_rhs_density(3.0, 2.0, Sector.POSITIVE, gravitational_constant=2.0),
            8.0 * np.pi,
        )
        self.assertAlmostEqual(
            poisson_rhs_density(3.0, 2.0, Sector.NEGATIVE, gravitational_constant=2.0),
            -8.0 * np.pi,
        )

    def test_balanced_absolute_densities_cancel_in_both_metrics(self) -> None:
        self.assertAlmostEqual(poisson_rhs_density(3.0, 3.0, Sector.POSITIVE), 0.0)
        self.assertAlmostEqual(poisson_rhs_density(3.0, 3.0, Sector.NEGATIVE), 0.0)

    def test_point_source_attraction_and_repulsion(self) -> None:
        source = PointSource(
            position=np.asarray([1.0, 0.0]),
            mass_abs=2.0,
            sector=Sector.POSITIVE,
        )

        same = point_source_acceleration(
            np.asarray([0.0, 0.0]),
            source,
            test_sector=Sector.POSITIVE,
        )
        opposite = point_source_acceleration(
            np.asarray([0.0, 0.0]),
            source,
            test_sector=Sector.NEGATIVE,
        )

        np.testing.assert_allclose(same, np.asarray([2.0, 0.0]))
        np.testing.assert_allclose(opposite, np.asarray([-2.0, 0.0]))

    def test_point_source_potential_has_expected_sign(self) -> None:
        source = PointSource(
            position=np.asarray([1.0]),
            mass_abs=2.0,
            sector=Sector.POSITIVE,
        )

        self.assertAlmostEqual(
            point_source_potential(np.asarray([0.0]), source, Sector.POSITIVE),
            -2.0,
        )
        self.assertAlmostEqual(
            point_source_potential(np.asarray([0.0]), source, Sector.NEGATIVE),
            2.0,
        )

    def test_opposite_pair_separates_instead_of_bondi_runaway(self) -> None:
        positive = PointSource(
            position=np.asarray([0.0]),
            mass_abs=1.0,
            sector=Sector.POSITIVE,
        )
        negative = PointSource(
            position=np.asarray([1.0]),
            mass_abs=1.0,
            sector=Sector.NEGATIVE,
        )

        a_positive = point_source_acceleration(
            positive.position,
            negative,
            test_sector=Sector.POSITIVE,
        )
        a_negative = point_source_acceleration(
            negative.position,
            positive,
            test_sector=Sector.NEGATIVE,
        )

        self.assertLess(a_positive[0], 0.0)
        self.assertGreater(a_negative[0], 0.0)

    def test_total_acceleration_sums_sources(self) -> None:
        sources = [
            PointSource(np.asarray([1.0, 0.0]), 1.0, Sector.POSITIVE),
            PointSource(np.asarray([-1.0, 0.0]), 1.0, Sector.POSITIVE),
        ]

        acceleration = total_acceleration(
            np.asarray([0.0, 0.0]),
            sources,
            test_sector=Sector.POSITIVE,
        )

        np.testing.assert_allclose(acceleration, np.asarray([0.0, 0.0]))

    def test_single_body_has_zero_acceleration(self) -> None:
        bodies = [
            BodyState(
                position=np.asarray([0.0]),
                velocity=np.asarray([0.0]),
                mass_abs=1.0,
                sector=Sector.POSITIVE,
            )
        ]

        accelerations = accelerations_for_bodies(bodies)

        np.testing.assert_allclose(accelerations[0], np.asarray([0.0]))

    def test_leapfrog_same_sector_pair_approaches(self) -> None:
        bodies = [
            BodyState(np.asarray([0.0]), np.asarray([0.0]), 1.0, Sector.POSITIVE),
            BodyState(np.asarray([1.0]), np.asarray([0.0]), 1.0, Sector.POSITIVE),
        ]

        updated = leapfrog_step(bodies, dt=0.1)

        self.assertGreater(updated[0].position[0], bodies[0].position[0])
        self.assertLess(updated[1].position[0], bodies[1].position[0])

    def test_leapfrog_opposite_sector_pair_separates(self) -> None:
        bodies = [
            BodyState(np.asarray([0.0]), np.asarray([0.0]), 1.0, Sector.POSITIVE),
            BodyState(np.asarray([1.0]), np.asarray([0.0]), 1.0, Sector.NEGATIVE),
        ]

        updated = leapfrog_step(bodies, dt=0.1)

        self.assertLess(updated[0].position[0], bodies[0].position[0])
        self.assertGreater(updated[1].position[0], bodies[1].position[0])

    def test_pair_potential_signs_follow_interaction(self) -> None:
        positive = BodyState(np.asarray([0.0]), np.asarray([0.0]), 2.0, Sector.POSITIVE)
        positive_other = BodyState(np.asarray([1.0]), np.asarray([0.0]), 3.0, Sector.POSITIVE)
        negative = BodyState(np.asarray([1.0]), np.asarray([0.0]), 3.0, Sector.NEGATIVE)

        self.assertAlmostEqual(pair_potential_energy(positive, positive_other), -6.0)
        self.assertAlmostEqual(pair_potential_energy(positive, negative), 6.0)

    def test_kinetic_energy(self) -> None:
        bodies = [
            BodyState(np.asarray([0.0]), np.asarray([2.0]), 3.0, Sector.POSITIVE),
            BodyState(np.asarray([1.0]), np.asarray([-1.0]), 4.0, Sector.NEGATIVE),
        ]

        self.assertAlmostEqual(kinetic_energy(bodies), 8.0)

    def test_leapfrog_energy_drift_is_small_for_short_run(self) -> None:
        bodies = [
            BodyState(np.asarray([-0.5]), np.asarray([0.0]), 1.0, Sector.POSITIVE),
            BodyState(np.asarray([0.5]), np.asarray([0.0]), 1.0, Sector.NEGATIVE),
        ]
        initial_energy = total_energy(bodies, softening=0.2)
        current = bodies
        for _ in range(20):
            current = leapfrog_step(current, dt=0.005, softening=0.2)

        self.assertLess(abs(total_energy(current, softening=0.2) - initial_energy), 1e-3)


if __name__ == "__main__":
    unittest.main()
