from __future__ import annotations

import unittest

import numpy as np

from janus_lab.quantum_sector import (
    BoundaryCondition,
    JanusQuantumModel1D,
    JanusQuantumState1D,
    SchrodingerPoissonRun1D,
    evolve_janus_state_1d,
    expectation_value_1d,
    finite_difference_laplacian_1d,
    gaussian_wavepacket_1d,
    harmonic_oscillator_potential_1d,
    janus_energy_expectation_1d,
    janus_bimetric_hamiltonian_1d,
    janus_sector_hamiltonian_1d,
    janus_schrodinger_poisson_hamiltonians_1d,
    janus_schrodinger_poisson_potentials_1d,
    janus_state_probability_1d,
    kinetic_operator_1d,
    momentum_expectation_1d,
    momentum_variance_1d,
    position_expectation_1d,
    position_variance_1d,
    normalize_janus_state_1d,
    normalize_wavefunction_1d,
    potential_energy_from_sources_1d,
    probability_current_1d,
    quantum_mass_densities_1d,
    run_schrodinger_poisson_1d,
    schrodinger_hamiltonian_1d,
    schrodinger_poisson_energy_1d,
    schrodinger_poisson_step_1d,
    sector_centroid_separation_1d,
    sector_probability_1d,
    solve_periodic_poisson_1d,
)
from janus_lab.signed_sector import PointSource, Sector


class QuantumSectorTests(unittest.TestCase):
    def test_kinetic_operator_stays_positive_for_sector_model(self) -> None:
        grid = np.linspace(-1.0, 1.0, 5)

        kinetic = kinetic_operator_1d(grid, mass_abs=2.0)

        np.testing.assert_allclose(kinetic, kinetic.T)
        self.assertGreaterEqual(float(np.min(np.linalg.eigvalsh(kinetic))), -1e-12)

    def test_potential_energy_uses_janus_interaction_signs(self) -> None:
        grid = np.asarray([0.0])
        positive_source = PointSource(np.asarray([1.0]), 2.0, Sector.POSITIVE)

        same = potential_energy_from_sources_1d(
            grid,
            test_mass_abs=3.0,
            test_sector=Sector.POSITIVE,
            sources=[positive_source],
        )
        opposite = potential_energy_from_sources_1d(
            grid,
            test_mass_abs=3.0,
            test_sector=Sector.NEGATIVE,
            sources=[positive_source],
        )

        np.testing.assert_allclose(same, np.asarray([-6.0]))
        np.testing.assert_allclose(opposite, np.asarray([6.0]))

    def test_negative_sector_source_attracts_negative_sector_state(self) -> None:
        grid = np.asarray([0.0])
        negative_source = PointSource(np.asarray([1.0]), 2.0, Sector.NEGATIVE)

        same = potential_energy_from_sources_1d(
            grid,
            test_mass_abs=1.5,
            test_sector=Sector.NEGATIVE,
            sources=[negative_source],
        )
        opposite = potential_energy_from_sources_1d(
            grid,
            test_mass_abs=1.5,
            test_sector=Sector.POSITIVE,
            sources=[negative_source],
        )

        np.testing.assert_allclose(same, np.asarray([-3.0]))
        np.testing.assert_allclose(opposite, np.asarray([3.0]))

    def test_bimetric_hamiltonian_has_no_off_diagonal_sector_mixing(self) -> None:
        grid = np.linspace(-2.0, 2.0, 5)
        source = PointSource(np.asarray([1.5]), 1.0, Sector.POSITIVE)

        block = janus_bimetric_hamiltonian_1d(
            grid,
            test_mass_abs=1.0,
            sources=[source],
            softening=0.25,
        )
        positive = janus_sector_hamiltonian_1d(
            grid,
            test_mass_abs=1.0,
            test_sector=Sector.POSITIVE,
            sources=[source],
            softening=0.25,
        )
        negative = janus_sector_hamiltonian_1d(
            grid,
            test_mass_abs=1.0,
            test_sector=Sector.NEGATIVE,
            sources=[source],
            softening=0.25,
        )
        n = grid.size

        np.testing.assert_allclose(block[:n, :n], positive)
        np.testing.assert_allclose(block[n:, n:], negative)
        np.testing.assert_allclose(block[:n, n:], np.zeros((n, n)))
        np.testing.assert_allclose(block[n:, :n], np.zeros((n, n)))

    def test_wavefunction_normalization_uses_grid_measure(self) -> None:
        grid = np.linspace(-1.0, 1.0, 5)
        psi = normalize_wavefunction_1d(grid, np.ones(grid.size))

        self.assertAlmostEqual(sector_probability_1d(grid, psi), 1.0)

    def test_janus_state_normalization_sums_both_sectors(self) -> None:
        grid = np.linspace(-1.0, 1.0, 5)
        state = JanusQuantumState1D(
            grid,
            np.ones(grid.size),
            1j * np.ones(grid.size),
            mass_abs=1.0,
        )

        normalized = normalize_janus_state_1d(state)

        self.assertAlmostEqual(janus_state_probability_1d(normalized), 1.0)
        self.assertAlmostEqual(sector_probability_1d(grid, normalized.positive), 0.5)
        self.assertAlmostEqual(sector_probability_1d(grid, normalized.negative), 0.5)

    def test_evolution_preserves_probability_without_sector_transfer(self) -> None:
        grid = np.linspace(-2.0, 2.0, 9)
        positive = normalize_wavefunction_1d(grid, np.exp(-(grid + 0.5) ** 2))
        state = JanusQuantumState1D(
            grid,
            positive,
            np.zeros(grid.size, dtype=complex),
            mass_abs=1.0,
        )
        source = PointSource(np.asarray([1.25]), 1.0, Sector.POSITIVE)

        evolved = evolve_janus_state_1d(state, [source], dt=0.05, softening=0.2)

        self.assertAlmostEqual(janus_state_probability_1d(evolved), 1.0)
        self.assertAlmostEqual(sector_probability_1d(grid, evolved.negative), 0.0)

    def test_energy_expectation_is_conserved_for_static_sources(self) -> None:
        grid = np.linspace(-2.0, 2.0, 9)
        state = normalize_janus_state_1d(
            JanusQuantumState1D(
                grid,
                np.exp(-(grid + 0.5) ** 2),
                1j * np.exp(-(grid - 0.5) ** 2),
                mass_abs=1.0,
            )
        )
        source = PointSource(np.asarray([1.25]), 1.0, Sector.NEGATIVE)

        initial = janus_energy_expectation_1d(state, [source], softening=0.2)
        evolved = evolve_janus_state_1d(state, [source], dt=0.05, softening=0.2)
        final = janus_energy_expectation_1d(evolved, [source], softening=0.2)

        self.assertAlmostEqual(final, initial)

    def test_model_facade_keeps_state_evolution_and_energy_together(self) -> None:
        grid = np.linspace(-2.0, 2.0, 9)
        source = PointSource(np.asarray([1.25]), 1.0, Sector.POSITIVE)
        model = JanusQuantumModel1D(
            grid,
            mass_abs=1.0,
            sources=(source,),
            softening=0.2,
        )
        state = model.normalize(
            model.state(
                np.exp(-(grid + 0.5) ** 2),
                np.zeros(grid.size, dtype=complex),
            )
        )

        evolved = model.evolve(state, dt=0.05)

        self.assertAlmostEqual(model.probability(evolved), 1.0)
        self.assertAlmostEqual(sector_probability_1d(grid, evolved.negative), 0.0)
        self.assertAlmostEqual(model.energy(evolved), model.energy(state))

    def test_model_rejects_state_from_other_grid(self) -> None:
        grid = np.linspace(-2.0, 2.0, 9)
        model = JanusQuantumModel1D(grid, mass_abs=1.0)
        other = JanusQuantumState1D(
            np.linspace(-1.0, 1.0, 9),
            np.ones(9),
            np.zeros(9),
            mass_abs=1.0,
        )

        with self.assertRaises(ValueError):
            model.probability(other)

    def test_gaussian_wavepacket_observables_match_inputs(self) -> None:
        grid = np.linspace(-8.0, 8.0, 801)
        psi = gaussian_wavepacket_1d(
            grid,
            center=0.75,
            width=0.9,
            momentum=1.2,
        )

        self.assertAlmostEqual(sector_probability_1d(grid, psi), 1.0)
        self.assertAlmostEqual(position_expectation_1d(grid, psi), 0.75, delta=1e-3)
        self.assertAlmostEqual(position_variance_1d(grid, psi), 0.9**2, delta=1e-3)
        self.assertAlmostEqual(momentum_expectation_1d(grid, psi), 1.2, delta=1e-3)
        self.assertAlmostEqual(
            momentum_variance_1d(grid, psi),
            1.0 / (4.0 * 0.9**2),
            delta=2e-3,
        )

    def test_probability_current_tracks_packet_momentum(self) -> None:
        grid = np.linspace(-8.0, 8.0, 801)
        mass = 2.0
        momentum = 1.4
        psi = gaussian_wavepacket_1d(
            grid,
            center=0.0,
            width=1.0,
            momentum=momentum,
        )

        density = np.abs(psi) ** 2
        current = probability_current_1d(grid, psi, mass_abs=mass)
        center_index = grid.size // 2

        self.assertAlmostEqual(
            current[center_index] / density[center_index],
            momentum / mass,
            delta=1e-3,
        )

    def test_harmonic_ground_packet_has_expected_energy(self) -> None:
        grid = np.linspace(-8.0, 8.0, 401)
        mass = 1.3
        omega = 0.7
        hbar = 1.0
        width = np.sqrt(hbar / (2.0 * mass * omega))
        psi = gaussian_wavepacket_1d(grid, center=0.0, width=width, hbar=hbar)
        potential = harmonic_oscillator_potential_1d(grid, mass, omega)
        hamiltonian = schrodinger_hamiltonian_1d(
            grid,
            mass,
            potential_energy=potential,
            hbar=hbar,
        )

        energy = expectation_value_1d(grid, psi, hamiltonian)

        self.assertAlmostEqual(energy.real, 0.5 * hbar * omega, delta=2e-3)
        self.assertAlmostEqual(energy.imag, 0.0)

    def test_periodic_laplacian_wraps_edges(self) -> None:
        grid = np.asarray([0.0, 1.0, 2.0, 3.0])

        laplacian = finite_difference_laplacian_1d(
            grid,
            boundary_condition=BoundaryCondition.PERIODIC,
        )

        self.assertEqual(laplacian[0, -1], 1.0)
        self.assertEqual(laplacian[-1, 0], 1.0)

    def test_free_packet_moves_with_expected_velocity(self) -> None:
        grid = np.linspace(-20.0, 20.0, 201)
        mass = 2.0
        momentum = 0.6
        dt = 0.2
        model = JanusQuantumModel1D(grid, mass_abs=mass)
        state = model.state(
            gaussian_wavepacket_1d(grid, center=-1.0, width=1.2, momentum=momentum),
            np.zeros(grid.size, dtype=complex),
        )

        evolved = model.evolve(state, dt=dt)

        self.assertAlmostEqual(
            position_expectation_1d(grid, evolved.positive),
            -1.0 + momentum * dt / mass,
            delta=0.02,
        )

    def test_periodic_poisson_solves_cosine_mode(self) -> None:
        grid = np.linspace(0.0, 2.0 * np.pi, 128, endpoint=False)
        density = np.cos(grid)

        potential = solve_periodic_poisson_1d(grid, density)

        np.testing.assert_allclose(potential, -4.0 * np.pi * np.cos(grid), atol=1e-12)

    def test_quantum_mass_densities_follow_sector_probabilities(self) -> None:
        grid = np.linspace(-4.0, 4.0, 128, endpoint=False)
        positive = gaussian_wavepacket_1d(grid, center=-1.0, width=0.5)
        negative = np.zeros(grid.size, dtype=complex)
        state = JanusQuantumState1D(grid, positive, negative, mass_abs=2.5)

        rho_positive, rho_negative = quantum_mass_densities_1d(state)

        self.assertAlmostEqual(np.sum(rho_positive) * (grid[1] - grid[0]), 2.5)
        self.assertAlmostEqual(np.sum(rho_negative) * (grid[1] - grid[0]), 0.0)

    def test_balanced_schrodinger_poisson_densities_cancel(self) -> None:
        grid = np.linspace(-4.0, 4.0, 128, endpoint=False)
        psi = gaussian_wavepacket_1d(grid, center=0.0, width=0.7)
        state = JanusQuantumState1D(grid, psi, psi, mass_abs=1.0)

        phi_positive, phi_negative = janus_schrodinger_poisson_potentials_1d(state)

        np.testing.assert_allclose(phi_positive, np.zeros_like(grid), atol=1e-12)
        np.testing.assert_allclose(phi_negative, np.zeros_like(grid), atol=1e-12)

    def test_schrodinger_poisson_potentials_are_conjugate(self) -> None:
        grid = np.linspace(-4.0, 4.0, 128, endpoint=False)
        state = JanusQuantumState1D(
            grid,
            gaussian_wavepacket_1d(grid, center=-1.0, width=0.5),
            gaussian_wavepacket_1d(grid, center=1.0, width=0.5),
            mass_abs=1.0,
        )

        phi_positive, phi_negative = janus_schrodinger_poisson_potentials_1d(state)

        np.testing.assert_allclose(phi_negative, -phi_positive)

    def test_schrodinger_poisson_step_preserves_sector_probabilities(self) -> None:
        grid = np.linspace(-6.0, 6.0, 96, endpoint=False)
        state = JanusQuantumState1D(
            grid,
            gaussian_wavepacket_1d(grid, center=-1.0, width=0.7, momentum=0.2),
            gaussian_wavepacket_1d(grid, center=1.0, width=0.7, momentum=-0.2),
            mass_abs=1.0,
        )

        evolved = schrodinger_poisson_step_1d(state, dt=0.01)

        self.assertAlmostEqual(
            sector_probability_1d(grid, evolved.positive),
            sector_probability_1d(grid, state.positive),
        )
        self.assertAlmostEqual(
            sector_probability_1d(grid, evolved.negative),
            sector_probability_1d(grid, state.negative),
        )

    def test_schrodinger_poisson_hamiltonians_are_sector_separate(self) -> None:
        grid = np.linspace(-4.0, 4.0, 32, endpoint=False)
        state = JanusQuantumState1D(
            grid,
            gaussian_wavepacket_1d(grid, center=-1.0, width=0.8),
            np.zeros(grid.size, dtype=complex),
            mass_abs=1.0,
        )

        positive_h, negative_h = janus_schrodinger_poisson_hamiltonians_1d(state)

        np.testing.assert_allclose(positive_h, positive_h.T.conj())
        np.testing.assert_allclose(negative_h, negative_h.T.conj())

    def test_schrodinger_poisson_energy_is_finite(self) -> None:
        grid = np.linspace(-6.0, 6.0, 96, endpoint=False)
        state = JanusQuantumState1D(
            grid,
            gaussian_wavepacket_1d(grid, center=-1.0, width=0.8),
            gaussian_wavepacket_1d(grid, center=1.0, width=0.8),
            mass_abs=1.0,
        )

        energy = schrodinger_poisson_energy_1d(state, gravitational_constant=0.05)

        self.assertTrue(np.isfinite(energy))

    def test_schrodinger_poisson_run_tracks_diagnostics(self) -> None:
        grid = np.linspace(-8.0, 8.0, 96, endpoint=False)
        state = JanusQuantumState1D(
            grid,
            gaussian_wavepacket_1d(grid, center=-1.0, width=0.7),
            gaussian_wavepacket_1d(grid, center=1.0, width=0.7),
            mass_abs=1.0,
        )

        run = run_schrodinger_poisson_1d(
            state,
            steps=3,
            dt=0.01,
            gravitational_constant=0.02,
        )

        self.assertIsInstance(run, SchrodingerPoissonRun1D)
        self.assertEqual(run.energies.shape, (4,))
        self.assertEqual(run.positive_probabilities.shape, (4,))
        self.assertEqual(run.negative_probabilities.shape, (4,))
        np.testing.assert_allclose(run.positive_probabilities, np.ones(4), atol=1e-12)
        np.testing.assert_allclose(run.negative_probabilities, np.ones(4), atol=1e-12)
        self.assertLess(abs(run.energy_drift), 1e-3)

    def test_opposite_sector_packets_begin_to_separate(self) -> None:
        grid = np.linspace(-8.0, 8.0, 96, endpoint=False)
        state = JanusQuantumState1D(
            grid,
            gaussian_wavepacket_1d(grid, center=-1.0, width=0.7),
            gaussian_wavepacket_1d(grid, center=1.0, width=0.7),
            mass_abs=1.0,
        )

        run = run_schrodinger_poisson_1d(
            state,
            steps=4,
            dt=0.02,
            gravitational_constant=0.08,
        )

        self.assertGreater(run.sector_separations[-1], run.sector_separations[0])
        self.assertAlmostEqual(run.sector_separations[0], sector_centroid_separation_1d(state))


if __name__ == "__main__":
    unittest.main()
