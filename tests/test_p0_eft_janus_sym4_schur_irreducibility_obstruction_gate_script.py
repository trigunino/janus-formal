import unittest

from janus_lab.janus_phase_space_occupation_search import (
    sym4_schur_irreducibility_obstruction_payload,
)


class JanusSym4SchurIrreducibilityObstructionGateTests(unittest.TestCase):
    def test_full_symmetry_forces_scalar_hamiltonian(self):
        payload = sym4_schur_irreducibility_obstruction_payload()

        self.assertTrue(payload["representation"]["irreducible_under_natural_action"])
        self.assertTrue(payload["schur_consequence"]["fully_symmetric_operator_is_scalar"])
        self.assertFalse(payload["schur_consequence"]["fully_symmetric_H_orders_1001_states"])

    def test_nontrivial_h_requires_derived_selector(self):
        payload = sym4_schur_irreducibility_obstruction_payload()

        self.assertTrue(payload["schur_consequence"]["nontrivial_H_requires_symmetry_breaking_or_external_generator"])
        self.assertEqual(payload["if_allowed_source_is_derived"]["z_max"], 1000.0)
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
