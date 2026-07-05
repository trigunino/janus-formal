import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_counterterm_component_from_inputs_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCountertermComponentFromInputsGateTests(unittest.TestCase):
    def test_missing_input_blocks_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json", output_path=Path(tmp) / "out.json")
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["counterterm_component_values_ready"])

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
                        "fitted_counterterm_coefficient_used": False,
                        "counterterm_FLRW_stress_reduced": True,
                        "counterterm_radial_reduction_ready": True,
                        "a_grid": [0.25, 0.5, 1.0],
                        "counterterm_rho": [0.1, 0.2, 0.3],
                        "counterterm_p": [0.4, 0.5, 0.6],
                        "counterterm_provenance": "active Sigma counterterm FLRW reduction",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["flrw_components_over_rho_crit0"]["counterterm_p"], [0.4, 0.5, 0.6])
        self.assertFalse(written["archived_z4_reuse_used"])

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
                        "fitted_counterterm_coefficient_used": False,
                        "counterterm_FLRW_stress_reduced": True,
                        "counterterm_radial_reduction_ready": True,
                        "a_grid": [0.25, 0.5, 1.0],
                        "counterterm_rho": [0.1, 0.2, 0.3],
                        "counterterm_p": [0.4, 0.5, 0.6],
                        "counterterm_provenance": "Planck LCDM fitted counterterm",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path=input_path, output_path=output_path)
        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])

    def test_missing_radial_reduction_proof_blocks(self):
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
                        "fitted_counterterm_coefficient_used": False,
                        "counterterm_FLRW_stress_reduced": True,
                        "counterterm_radial_reduction_ready": False,
                        "a_grid": [0.25, 0.5, 1.0],
                        "counterterm_rho": [0.1, 0.2, 0.3],
                        "counterterm_p": [0.4, 0.5, 0.6],
                        "counterterm_provenance": "active Sigma counterterm FLRW reduction",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path=input_path, output_path=output_path)
        self.assertFalse(payload["gate_passed"])
        self.assertIn("counterterm_radial_reduction_ready", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
