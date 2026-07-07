import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_primitive_sector_n_selection_gate import build_payload


class PrimitiveSectorNSelectionGateTests(unittest.TestCase):
    def test_live_primitive_selection_is_blocked(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["primitive_n_selected"])
        self.assertIn("zero_sector_excluded_by_nontrivial_throat", payload["blocked_by"])

    def test_selects_n_one_when_internal_conditions_hold(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            inp = root / "inputs.json"
            out = root / "frontier.json"
            inp.write_text(
                json.dumps(
                    {
                        "sector_lattice_exists": True,
                        "zero_sector_excluded_by_nontrivial_throat": True,
                        "fusion_channels_forbidden": True,
                        "splitting_channels_forbidden": True,
                        "empty_punctures_forbidden": True,
                        "ground_state_energy_monotone_in_abs_n": True,
                        "orientation_identifies_plus_minus_n": True,
                        "primitive_sector_internal_provenance": True,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=inp, output_path=out, write_output=True)

        self.assertTrue(payload["primitive_n_selected"])
        self.assertEqual(payload["selected_n"], 1)


if __name__ == "__main__":
    unittest.main()
