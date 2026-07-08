import unittest

from scripts.build_p0_eft_janus_quantum_first_alpha_spectrum_gate import (
    build_payload as build_alpha,
)
from scripts.build_p0_eft_janus_quantum_first_classical_limit_gate import (
    build_payload as build_limit,
)
from scripts.build_p0_eft_janus_quantum_first_cp1_tqft_phase_space_gate import (
    build_payload as build_phase,
)
from scripts.build_p0_eft_janus_quantum_first_verdict_gate import (
    build_payload as build_verdict,
)


class QuantumFirstBoundaryStateTests(unittest.TestCase):
    def test_cp1_labels_are_available_but_energy_scale_is_not(self):
        payload = build_phase()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["quantum_labels_available"])
        self.assertFalse(payload["physical_energy_scale_available"])
        self.assertIn("j_to_alpha_map", payload["cp1_route"]["missing"])

    def test_alpha_spectrum_is_conditional_not_predictive(self):
        payload = build_alpha()

        self.assertTrue(payload["conditional_alpha_spectrum_ready"])
        self.assertFalse(payload["predictive_alpha_spectrum_ready"])
        self.assertIn(
            "boundary_mass_operator_or_energy_function_not_derived",
            payload["blocked_by"],
        )

    def test_classical_limit_is_conditional(self):
        payload = build_limit()

        self.assertTrue(payload["conditional_classical_limit_ready"])
        self.assertFalse(payload["no_fit_classical_janus_ready"])

    def test_verdict_keeps_branch_non_closed(self):
        payload = build_verdict()

        self.assertEqual(payload["branch_status"], "conditional_quantum_spectrum_only")
        self.assertFalse(payload["no_fit_alpha_generated"])
        self.assertIn(
            "derive_boundary_mass_operator_from_quantum_state",
            payload["next_non_rustine_targets"],
        )


if __name__ == "__main__":
    unittest.main()
