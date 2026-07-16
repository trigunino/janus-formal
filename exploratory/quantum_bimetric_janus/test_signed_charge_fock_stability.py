import unittest

import numpy as np

from signed_charge_fock_stability import (
    exact_ground_energy,
    exact_signed_susceptibility,
    ghost_hamiltonian,
    ground_state,
    ground_energy,
    normal_mode_frequencies,
    positive_hamiltonian,
    pt_odd_source_operator,
    signed_charge,
    sourced_positive_hamiltonian,
    swap_operator,
)


class SignedChargeFockStabilityTests(unittest.TestCase):
    def test_positive_model_ground_energy_converges_with_cutoff(self):
        energies = [ground_energy(positive_hamiltonian(n)) for n in (4, 6, 8, 10)]
        self.assertLess(max(abs(x - energies[-1]) for x in energies[-2:]), 1e-8)
        self.assertGreater(energies[-1], 0.0)

    def test_ghost_control_runs_to_minus_infinity_with_cutoff(self):
        energies = [ground_energy(ghost_hamiltonian(n)) for n in (4, 6, 8, 10)]
        self.assertTrue(np.allclose(energies, [-3.0, -5.0, -7.0, -9.0]))

    def test_sector_swap_preserves_hamiltonian_and_reverses_charge(self):
        cutoff = 6
        swap = swap_operator(cutoff)
        hamiltonian = positive_hamiltonian(cutoff)
        charge = signed_charge(cutoff)
        self.assertTrue(np.allclose(swap @ hamiltonian @ swap, hamiltonian))
        self.assertTrue(np.allclose(swap @ charge @ swap, -charge))

    def test_unstable_quadratic_form_is_rejected(self):
        with self.assertRaises(ValueError):
            positive_hamiltonian(4, coupling=1.0)

    def test_fock_ground_energy_matches_exact_normal_modes(self):
        numeric = ground_energy(positive_hamiltonian(12, coupling=0.2))
        self.assertAlmostEqual(numeric, exact_ground_energy(coupling=0.2), places=12)
        self.assertTrue(np.allclose(normal_mode_frequencies(coupling=0.2), np.sqrt([1.2, 0.8])))

    def test_combined_pt_maps_external_field_to_its_opposite(self):
        cutoff = 6
        swap = swap_operator(cutoff)
        positive_field = sourced_positive_hamiltonian(cutoff, field=0.05)
        negative_field = sourced_positive_hamiltonian(cutoff, field=-0.05)
        self.assertTrue(np.allclose(swap @ positive_field @ swap, negative_field))

    def test_signed_response_matches_exact_susceptibility(self):
        cutoff = 14
        field = 1e-4
        _, state = ground_state(sourced_positive_hamiltonian(cutoff, field=field))
        charge = pt_odd_source_operator(cutoff)
        response = float(np.vdot(state, charge @ state).real / field)
        self.assertAlmostEqual(response, exact_signed_susceptibility(), places=8)

    def test_source_lowers_vacuum_energy_quadratically_without_unbounding_it(self):
        cutoff = 12
        field = 0.05
        base = ground_energy(sourced_positive_hamiltonian(cutoff))
        shifted = ground_energy(sourced_positive_hamiltonian(cutoff, field=field))
        expected_shift = -(field**2) / (1.0 - 0.2)
        self.assertAlmostEqual(shifted - base, expected_shift, places=11)
        self.assertGreater(shifted, 0.0)


if __name__ == "__main__":
    unittest.main()
