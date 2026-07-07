import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_boundary_projection_charge_contract_gate import (
    build_payload,
)


class BoundaryProjectionChargeContractGateTests(unittest.TestCase):
    def test_missing_input_blocks_without_projected_charge(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                input_path=root / "missing.json",
                projected_output_path=root / "projected.json",
            )

        self.assertFalse(payload["input_exists"])
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["projected_boundary_charge_ready"])
        self.assertIn(
            "provide_active_z2_sigma_boundary_projection_json",
            payload["next_required"],
        )

    def test_valid_boundary_projection_reduces_reference_charge(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "active_z2_sigma_boundary_projection.json"
            output_path = root / "projected_boundary_charge_inputs.json"
            input_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "k": 1,
                        "a_grid": [0.5, 1.0],
                        "R_Sigma_abs_m": 2.0,
                        "Q_boundary_raw": [5.0, 7.0],
                        "Q_reference_raw": [2.0, 1.0],
                        "V_eff_m3": [3.0, 2.0],
                        "kappa_Z2Sigma": 1.0,
                        "reference_type": "Milne",
                        "Q_reference_zero_on_reference": True,
                        "Q_raw_kind": "mass_kg",
                        "C_BY": 1.0,
                        "action_signature": "Palatini+boundary-choice+projection",
                        "provenance": {
                            "compressed_planck_lcdm_background_used": False,
                            "archived_z4_reuse_used": False,
                            "observational_H0_fit_used": False,
                            "fitted_density_used": False,
                        },
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                input_path=input_path,
                projected_output_path=output_path,
                write_projected=True,
            )
            output_exists = output_path.exists()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["projected_boundary_charge_ready"])
        self.assertEqual(payload["reduction"]["Q_ren_raw"], [3.0, 6.0])
        self.assertEqual(payload["reduction"]["rho_eff_kg_m3"], [1.0, 3.0])
        self.assertTrue(output_exists)

    def test_fit_provenance_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "active_z2_sigma_boundary_projection.json"
            input_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "k": 1,
                        "a_grid": [1.0],
                        "R_Sigma_abs_m": 2.0,
                        "Q_boundary_raw": [5.0],
                        "Q_reference_raw": [2.0],
                        "V_eff_m3": [3.0],
                        "kappa_Z2Sigma": 1.0,
                        "reference_type": "Milne",
                        "Q_reference_zero_on_reference": True,
                        "Q_raw_kind": "mass_kg",
                        "C_BY": 1.0,
                        "action_signature": "Palatini+boundary-choice+projection",
                        "provenance": {
                            "compressed_planck_lcdm_background_used": False,
                            "archived_z4_reuse_used": False,
                            "observational_H0_fit_used": True,
                            "fitted_density_used": False,
                        },
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path=input_path)

        self.assertFalse(payload["gate_passed"])
        self.assertIn(
            "forbidden_provenance:observational_H0_fit_used",
            payload["validation_errors"],
        )


if __name__ == "__main__":
    unittest.main()
