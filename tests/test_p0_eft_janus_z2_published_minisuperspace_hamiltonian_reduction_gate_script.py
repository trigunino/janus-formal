import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_published_minisuperspace_hamiltonian_reduction_gate import (
    build_payload,
)


class PublishedMinisuperspaceHamiltonianReductionGateTests(unittest.TestCase):
    def test_live_status_is_continuous_casimir_not_quantized(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["canonical_hamiltonian_reduction_ready"])
        self.assertFalse(payload["alpha_quantization_ready"])
        self.assertEqual(payload["classification"], "continuous_Casimir_charge")
        self.assertIn("minisuperspace_lagrangian_written", payload["blocked_by"])
        self.assertIn("compact_cycle_in_reduced_orbit_found", payload["blocked_by"])

    def test_complete_inputs_allow_quantized_or_selected_sector(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(
                json.dumps(
                    {
                        "minisuperspace_lagrangian_written": True,
                        "lapse_constraints_derived": True,
                        "canonical_momenta_derived": True,
                        "hamiltonian_constraint_derived": True,
                        "constraint_reduction_performed": True,
                        "symplectic_pullback_to_exact_solution_derived": True,
                        "alpha_conjugate_coordinate_identified": True,
                        "compact_cycle_in_reduced_orbit_found": True,
                        "action_integral_I_alpha_derived": True,
                        "integrality_or_selection_law_derived": True,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(path)

        self.assertTrue(payload["canonical_hamiltonian_reduction_ready"])
        self.assertTrue(payload["alpha_quantization_ready"])
        self.assertEqual(payload["classification"], "quantized_or_selected_sector")


if __name__ == "__main__":
    unittest.main()
