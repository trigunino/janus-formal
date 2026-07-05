import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_zero_component_from_transparency_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaMatterFluxZeroComponentFromTransparencyGateTests(unittest.TestCase):
    def test_missing_input_blocks_zero_component_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                output_path=Path(tmp) / "out.json",
            )

        self.assertFalse(payload["input_exists"])
        self.assertFalse(payload["matter_flux_rho_p_values_ready"])
        self.assertFalse(payload["zero_component_output_written"])
        self.assertFalse(payload["gate_passed"])
        self.assertIn("transparency_input_writer", payload["upstream_frontiers"])
        self.assertTrue(payload["nearest_zero_matter_flux_frontier"]["diagnostic_only"])

    def test_transparency_input_writes_zero_component_payload(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "transparency.json"
            output_path = Path(tmp) / "matter_flux.json"
            input_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "active_sigma_transparency_derived": True,
                        "a_grid": [0.25, 0.5, 1.0],
                        "transparency_provenance": "active Sigma normal-flux cancellation proof",
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["matter_flux_rho_p_values_ready"])
        self.assertEqual(written["flrw_components_over_rho_crit0"]["matter_flux_rho"], [0.0, 0.0, 0.0])
        self.assertEqual(written["flrw_components_over_rho_crit0"]["matter_flux_p"], [0.0, 0.0, 0.0])
        self.assertEqual(written["component_route"], "transparent_sigma_zero_flux")

    def test_transparency_false_blocks_zero_payload(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "transparency.json"
            output_path = Path(tmp) / "matter_flux.json"
            input_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "active_sigma_transparency_derived": False,
                        "a_grid": [0.25, 0.5, 1.0],
                        "transparency_provenance": "active Sigma normal-flux cancellation proof",
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                        "phenomenological_holst_bao_scan_used": False,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(input_path=input_path, output_path=output_path)

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["matter_flux_rho_p_values_ready"])
        self.assertIn("active Sigma transparency", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
