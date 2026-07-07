import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_chi_ll_casimir_topological_exit_gate import build_payload


class ChiLLCasimirTopologicalExitGateTests(unittest.TestCase):
    def test_default_blocks_without_active_inputs(self):
        payload = build_payload(Path("missing-casimir-input.json"))

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["casimir_exit_prediction_ready"])
        self.assertIn("quantum_field_content_declared", payload["blocked_by"])
        self.assertIn("casimir_coefficient_C", payload["blocked_by"])

    def test_forbids_observational_shortcuts(self):
        shortcuts = build_payload(Path("missing-casimir-input.json"))["forbidden_shortcuts"]

        self.assertTrue(shortcuts["choose_C_to_fit_H0"])
        self.assertTrue(shortcuts["choose_R_s_to_fit_observations"])
        self.assertTrue(shortcuts["ignore_renormalization_reference"])

    def test_derives_chi_if_all_inputs_are_supplied(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "casimir.json"
            path.write_text(
                json.dumps(
                    {
                        "compact_throat_topology_declared": True,
                        "quantum_field_content_declared": True,
                        "boundary_conditions_declared": True,
                        "renormalization_reference_declared": True,
                        "casimir_coefficient_C": 2.0,
                        "R_s_m": 4.0,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertTrue(payload["casimir_exit_prediction_ready"])
        self.assertTrue(payload["chi_LL_prediction_ready"])
        self.assertAlmostEqual(
            payload["derivation"]["chi_LL_abs_inverse_m"],
            1.0 / (8.0 * math.pi * 4.0),
        )


if __name__ == "__main__":
    unittest.main()
