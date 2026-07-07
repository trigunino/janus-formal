import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_null_sigma_bulk_rs_to_global_mass_gate import (
    build_payload,
)
from scripts.build_p0_eft_janus_z2_null_sigma_mass_charge_to_rs_gate import (
    C_SI,
    G_SI,
)


class NullSigmaBulkRsToGlobalMassGateTests(unittest.TestCase):
    def test_missing_bulk_rs_blocks_global_mass(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["bulk_Rs_solution_available"])
        self.assertIn(
            "derive_absolute_R_s_m_from_active_Schwarzschild_PT_bulk_solution",
            payload["next_required"],
        )

    def test_active_bulk_rs_writes_pt_paired_global_mass(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "bulk_rs.json"
            output_path = root / "global_mass.json"
            input_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "branch": "Z2_null_Sigma_PT_bridge",
                        "source": "active_derived",
                        "bulk_solution_kind": "Schwarzschild_PT_bridge",
                        "R_s_m": 2.0,
                        "R_s_provenance": "active_bulk_solution_radius",
                        "PT_energy_sign_reversal_proved": True,
                        "R_Sigma_equals_R_s_proved": True,
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
            expected_mass = C_SI * C_SI * 2.0 / (2.0 * G_SI)
            output_exists = output_path.exists()

        self.assertTrue(payload["gate_passed"])
        self.assertAlmostEqual(
            payload["global_mass_payload"]["M_plus_kg"], expected_mass
        )
        self.assertAlmostEqual(
            payload["global_mass_payload"]["M_minus_kg"], -expected_mass
        )
        self.assertTrue(output_exists)

    def test_fit_provenance_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "bulk_rs.json"
            input_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "branch": "Z2_null_Sigma_PT_bridge",
                        "source": "active_derived",
                        "bulk_solution_kind": "Schwarzschild_PT_bridge",
                        "R_s_m": 2.0,
                        "R_s_provenance": "fit_radius",
                        "PT_energy_sign_reversal_proved": True,
                        "R_Sigma_equals_R_s_proved": True,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn(
            "R_s_provenance_missing_or_forbidden", payload["validation_errors"]
        )


if __name__ == "__main__":
    unittest.main()
