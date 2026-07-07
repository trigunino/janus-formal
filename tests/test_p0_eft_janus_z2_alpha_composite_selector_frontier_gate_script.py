import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_alpha_composite_selector_frontier_gate import (
    build_payload,
)


class AlphaCompositeSelectorFrontierGateTests(unittest.TestCase):
    def test_live_frontier_identifies_missing_quantum_state_theorems(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["m_charge_ready"])
        self.assertFalse(payload["primitive_n_ready"])
        self.assertIn("minimal_mass_unit_derived", payload["current_frontier"])
        self.assertIn("n_equals_one_selected", payload["current_frontier"])

    def test_unique_selector_ready_when_both_frontiers_are_supplied(self):
        with tempfile.TemporaryDirectory() as tmp:
            inp = Path(tmp) / "frontier.json"
            inp.write_text(
                json.dumps(
                    {
                        "charge_lattice_integrality_derived": True,
                        "minimal_mass_unit_derived": True,
                        "unit_value_kg_derived": True,
                        "nonzero_sector_required": True,
                        "fusion_splitting_forbidden": True,
                        "n_equals_one_selected": True,
                        "selection_provenance_internal": True,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=inp)

        self.assertTrue(payload["m_charge_ready"])
        self.assertTrue(payload["primitive_n_ready"])
        self.assertTrue(payload["unique_alpha_selector_ready"])


if __name__ == "__main__":
    unittest.main()
