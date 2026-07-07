import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_null_sigma_global_noether_souriau_mass_bridge_gate import (
    build_payload,
)


class NullSigmaGlobalNoetherSouriauMassBridgeGateTests(unittest.TestCase):
    def test_missing_global_mass_solution_blocks_bridge_mass(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["M_bridge_available"])
        self.assertFalse(
            payload["bimetric_noether_result"]["absolute_magnitude_fixed_by_symmetry"]
        )
        self.assertIn(
            "derive_M_plus_kg_from_active_bimetric_bulk_solution_or_Noether_state",
            payload["next_required"],
        )

    def test_active_pt_paired_global_mass_writes_bridge_mass(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "global_mass.json"
            output_path = root / "mass_charge.json"
            input_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "branch": "Z2_null_Sigma_PT_bridge",
                        "source": "active_derived",
                        "M_plus_kg": 7.0,
                        "M_minus_kg": -7.0,
                        "PT_energy_sign_reversal_proved": True,
                        "bimetric_global_solution_proved": True,
                        "M_bridge_role": "bulk_solution_or_Noether_state_label",
                        "M_bridge_provenance": "active_bimetric_bulk_solution_mass",
                        "observational_fit_used": False,
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(
                input_path=input_path,
                output_path=output_path,
                write_output=True,
            )
            output_exists = output_path.exists()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["mass_payload"]["M_bridge_kg"], 7.0)
        self.assertTrue(output_exists)

    def test_wrong_pt_pairing_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "global_mass.json"
            input_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "branch": "Z2_null_Sigma_PT_bridge",
                        "source": "active_derived",
                        "M_plus_kg": 7.0,
                        "M_minus_kg": -6.0,
                        "PT_energy_sign_reversal_proved": True,
                        "bimetric_global_solution_proved": True,
                        "M_bridge_role": "bulk_solution_or_Noether_state_label",
                        "M_bridge_provenance": "active_bimetric_bulk_solution_mass",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn(
            "Souriau_PT_mass_pair_must_satisfy_M_minus_equals_minus_M_plus",
            payload["validation_errors"],
        )


if __name__ == "__main__":
    unittest.main()
