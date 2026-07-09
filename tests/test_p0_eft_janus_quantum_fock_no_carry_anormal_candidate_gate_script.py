import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    quantum_fock_no_carry_anormal_candidate_payload,
)


class JanusQuantumFockNoCarryANormalCandidateGateTests(unittest.TestCase):
    def test_no_carry_operator_orders_sym4(self):
        payload = quantum_fock_no_carry_anormal_candidate_payload()
        self.assertEqual(payload["inputs"]["base"], 5)
        self.assertEqual(payload["spectrum"]["target_levels"], 1001)
        self.assertEqual(payload["spectrum"]["distinct_levels"], 1001)
        self.assertTrue(payload["spectrum"]["orders_all_Sym4_states"])

    def test_not_promoted_without_janus_derivation(self):
        payload = quantum_fock_no_carry_anormal_candidate_payload()
        self.assertFalse(payload["no_fit_closed_now"])
        self.assertIn("ordered 11-mode basis", " ".join(payload["not_yet_derived_from_janus"]))


if __name__ == "__main__":
    unittest.main()
