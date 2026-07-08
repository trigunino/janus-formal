import unittest

from scripts.build_p0_eft_janus_quantum_first_boundary_mass_operator_no_go_gate import (
    build_payload as build_mass_no_go,
)
from scripts.build_p0_eft_janus_quantum_first_exhaustion_verdict_gate import (
    build_payload as build_exhaustion,
)


class QuantumFirstExhaustionTests(unittest.TestCase):
    def test_mass_operator_routes_are_audited_but_not_derived(self):
        payload = build_mass_no_go()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(all(payload["routes_exhausted"].values()))
        self.assertFalse(payload["boundary_mass_operator_derived"])
        self.assertFalse(payload["dimensionful_energy_unit_derived"])
        self.assertIn("cp1_casimir", payload["routes_exhausted"])
        self.assertIn("closed_tqft_hamiltonian", payload["routes_exhausted"])

    def test_final_verdict_is_exhausted_but_not_no_fit(self):
        payload = build_exhaustion()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["all_quantum_first_routes_audited"])
        self.assertTrue(payload["conditional_alpha_spectrum_ready"])
        self.assertTrue(payload["conditional_classical_limit_ready"])
        self.assertFalse(payload["boundary_mass_operator_derived"])
        self.assertFalse(payload["no_fit_alpha_generated"])
        self.assertEqual(
            payload["final_branch_status"],
            "exhausted_conditional_spectrum_no_alpha_prediction",
        )


if __name__ == "__main__":
    unittest.main()
