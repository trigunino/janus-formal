import unittest

import numpy as np

from signed_charge_fock_stability import (
    ghost_hamiltonian,
    ground_energy,
    positive_hamiltonian,
    signed_charge,
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


if __name__ == "__main__":
    unittest.main()
