import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_holst_nieh_yan_component_from_inputs_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaHolstNiehYanComponentFromInputsGateTests(unittest.TestCase):
    def test_missing_input_blocks_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                radial_zero_path=Path(tmp) / "missing_radial.json",
                output_path=Path(tmp) / "out.json",
            )
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["holst_nieh_yan_component_values_ready"])

    def test_active_input_writes_component(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "input.json"
            output_path = Path(tmp) / "out.json"
            input_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                        "a_grid": [0.25, 0.5, 1.0],
                        "holst_nieh_yan_rho": [0.1, 0.2, 0.3],
                        "holst_nieh_yan_p": [0.4, 0.5, 0.6],
                        "holst_nieh_yan_provenance": "active torsion pullback FLRW reduction",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["flrw_components_over_rho_crit0"]["holst_nieh_yan_rho"], [0.1, 0.2, 0.3])
        self.assertFalse(written["archived_z4_reuse_used"])

    def test_radial_zero_identity_writes_zero_component(self):
        with tempfile.TemporaryDirectory() as tmp:
            radial_path = Path(tmp) / "radial.json"
            output_path = Path(tmp) / "out.json"
            radial_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                        "a_grid": [0.25, 0.5],
                        "torsionless_Nieh_Yan_zero_identity_ready": True,
                        "E_HolstNiehYan_values": [0.0, 0.0],
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                radial_zero_path=radial_path,
                output_path=output_path,
            )
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["selected_input_route"], "torsionless_radial_zero_identity")
        self.assertEqual(written["flrw_components_over_rho_crit0"]["holst_nieh_yan_rho"], [0.0, 0.0])

    def test_forbidden_provenance_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "input.json"
            output_path = Path(tmp) / "out.json"
            input_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                        "a_grid": [0.25, 0.5, 1.0],
                        "holst_nieh_yan_rho": [0.1, 0.2, 0.3],
                        "holst_nieh_yan_p": [0.4, 0.5, 0.6],
                        "holst_nieh_yan_provenance": "archived Z4 coefficient",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path=input_path, output_path=output_path)
        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
