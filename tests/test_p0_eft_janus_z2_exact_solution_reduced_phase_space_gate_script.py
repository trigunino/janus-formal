import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_exact_solution_reduced_phase_space_gate import (
    alpha_from_global_energy_mass,
    build_payload,
    global_energy_mass_from_alpha,
)


class ExactSolutionReducedPhaseSpaceGateTests(unittest.TestCase):
    def test_live_classifies_alpha_as_continuous_charge_label(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["alpha_classification"], "continuous_global_charge_label")
        self.assertFalse(payload["canonical_reduced_phase_space_ready"])
        self.assertIn("reduced_action_derived", payload["blocked_by"])

    def test_alpha_energy_inverse_relations(self):
        mass = global_energy_mass_from_alpha(alpha_m=2.0, c_m_s=3.0, g_si=5.0)
        alpha = alpha_from_global_energy_mass(mass_kg=mass, c_m_s=3.0, g_si=5.0)

        self.assertAlmostEqual(mass, -9.0 / (5.0 * math.pi))
        self.assertAlmostEqual(alpha, 2.0)

    def test_complete_quantized_inputs_change_classification(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(
                json.dumps(
                    {
                        "reduced_action_derived": True,
                        "canonical_pair_derived": True,
                        "symplectic_form_derived": True,
                        "hamiltonian_constraint_derived": True,
                        "alpha_conjugate_variable_identified": True,
                        "compact_global_cycle_identified": True,
                        "integrality_or_state_selection_law_derived": True,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(path)

        self.assertEqual(payload["alpha_classification"], "quantized_or_selected_state")
        self.assertTrue(payload["alpha_quantized_or_selected"])


if __name__ == "__main__":
    unittest.main()
