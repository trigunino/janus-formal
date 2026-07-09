import unittest

from janus_lab.janus_phase_space_occupation_search import (
    sym4_diagonal_hamiltonian_ordering_audit_payload,
)


class JanusSym4DiagonalHamiltonianOrderingAuditGateTests(unittest.TestCase):
    def test_isotropic_block_weights_are_too_degenerate(self):
        payload = sym4_diagonal_hamiltonian_ordering_audit_payload()
        cases = {row["case"]: row for row in payload["diagonal_hamiltonian_cases"]}

        self.assertEqual(payload["inputs"]["basis_dimension"], 1001)
        self.assertEqual(cases["isotropic_block_weights"]["max_distinct_profiles"], 70)
        self.assertFalse(cases["isotropic_block_weights"]["can_order_all_1001_states"])

    def test_full_ordering_requires_extra_selector(self):
        payload = sym4_diagonal_hamiltonian_ordering_audit_payload()

        self.assertFalse(payload["no_fit_conclusion"]["isotropic_M31_diagonal_generator_orders_all_states"])
        self.assertTrue(payload["no_fit_conclusion"]["full_ordering_requires_extra_selector"])
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
