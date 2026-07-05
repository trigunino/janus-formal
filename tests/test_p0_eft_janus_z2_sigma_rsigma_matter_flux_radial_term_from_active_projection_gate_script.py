import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_rsigma_matter_flux_radial_term_from_active_projection_gate import (
    build_payload,
)


def _projection_input(**overrides):
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "active_flux_projection_ready": True,
        "matter_flux_radial_reduction_ready": True,
        "selected_route": "active_projection",
        "a_grid": [0.25, 0.5, 1.0],
        "E_matterFlux_values": [1.0, -0.5, 0.25],
    }
    payload.update(overrides)
    return payload


class RSigmaMatterFluxRadialTermFromActiveProjectionGateTests(unittest.TestCase):
    def test_writes_radial_term_from_active_projection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "projection.json"
            output = root / "matter.json"
            source.write_text(json.dumps(_projection_input()), encoding="utf-8")

            payload = build_payload(input_path=source, output_path=output)
            written = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["E_matterFlux_from_active_projection_written"])
        self.assertEqual(written["term_name"], "E_matterFlux")
        self.assertEqual(written["term_values"], [1.0, -0.5, 0.25])

    def test_blocks_without_projection_readiness(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "projection.json"
            source.write_text(
                json.dumps(_projection_input(active_flux_projection_ready=False)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("active_flux_projection_ready", payload["validation_error"])

    def test_blocks_without_active_projection_route_selection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "projection.json"
            source.write_text(
                json.dumps(_projection_input(selected_route="transparent")),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("selected_route", payload["validation_error"])

    def test_transparency_route_prevents_active_projection_overwrite(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "projection.json"
            transparency = root / "transparency.json"
            source.write_text(json.dumps(_projection_input()), encoding="utf-8")
            transparency.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "active_derived",
                        "active_sigma_transparency_derived": True,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(
                input_path=source,
                transparency_input_path=transparency,
                output_path=root / "out.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["transparency_route_already_derived"])
        self.assertIn("route-exclusive", payload["validation_error"])

    def test_forbidden_provenance_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "projection.json"
            source.write_text(
                json.dumps(_projection_input(archived_z4_reuse_used=True)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])


if __name__ == "__main__":
    unittest.main()
