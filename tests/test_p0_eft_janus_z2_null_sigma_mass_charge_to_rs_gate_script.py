import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_null_sigma_mass_charge_to_rs_gate import (
    G_SI,
    C_SI,
    build_payload,
)


class NullSigmaMassChargeToRsGateTests(unittest.TestCase):
    def test_missing_mass_charge_blocks_rs_selection(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["mass_charge_available"])
        self.assertFalse(payload["absolute_Rs_selected"])
        self.assertIn(
            "derive_active_null_bridge_mass_charge_M_bridge_kg",
            payload["next_required"],
        )

    def test_active_mass_charge_selects_rs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "mass.json"
            output_path = root / "rs.json"
            input_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "branch": "Z2_null_Sigma_PT_bridge",
                        "source": "active_derived",
                        "M_bridge_kg": 3.0,
                        "M_bridge_provenance": "derived_null_bridge_state_charge",
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
        self.assertTrue(payload["absolute_Rs_selected"])
        self.assertAlmostEqual(
            payload["rs_payload"]["R_s_m"], 2.0 * G_SI * 3.0 / (C_SI * C_SI)
        )
        self.assertTrue(output_exists)

    def test_fit_provenance_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "mass.json"
            input_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "branch": "Z2_null_Sigma_PT_bridge",
                        "source": "active_derived",
                        "M_bridge_kg": 3.0,
                        "M_bridge_provenance": "BAO_fit_mass",
                        "observational_fit_used": False,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn(
            "M_bridge_provenance_contains_forbidden_token",
            payload["validation_errors"],
        )


if __name__ == "__main__":
    unittest.main()
