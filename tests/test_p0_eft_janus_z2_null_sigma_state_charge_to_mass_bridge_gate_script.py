import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_null_sigma_state_charge_to_mass_bridge_gate import (
    build_payload,
)


class NullSigmaStateChargeToMassBridgeGateTests(unittest.TestCase):
    def test_missing_state_mass_inputs_block_mass_bridge(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["M_bridge_available"])
        self.assertIn(
            "derive_N_occ_Z2Sigma_from_boundary_state_or_superselection",
            payload["next_required"],
        )

    def test_active_state_mass_inputs_compute_bridge_mass(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "state_mass.json"
            output_path = root / "mass_charge.json"
            input_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "branch": "Z2_null_Sigma_PT_bridge",
                        "source": "active_derived",
                        "N_occ_Z2Sigma": 4.0,
                        "m_bridge_unit_kg": 2.5,
                        "mass_sign_policy": "PT_abs_mass_for_radius",
                        "N_occ_provenance": "boundary_state_superselection",
                        "m_bridge_unit_provenance": "active_bridge_matter_unit",
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
        self.assertTrue(payload["M_bridge_available"])
        self.assertEqual(payload["mass_payload"]["M_bridge_kg"], 10.0)
        self.assertTrue(output_exists)

    def test_fit_provenance_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "state_mass.json"
            input_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "branch": "Z2_null_Sigma_PT_bridge",
                        "source": "active_derived",
                        "N_occ_Z2Sigma": 4.0,
                        "m_bridge_unit_kg": 2.5,
                        "mass_sign_policy": "PT_abs_mass_for_radius",
                        "N_occ_provenance": "fit_state",
                        "m_bridge_unit_provenance": "active_bridge_matter_unit",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn(
            "N_occ_provenance_missing_or_forbidden",
            payload["validation_errors"],
        )


if __name__ == "__main__":
    unittest.main()
