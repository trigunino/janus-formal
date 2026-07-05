import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_active_projection_radial_input_writer_gate import (
    build_payload,
)


def _source(**overrides):
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "a_grid": [0.5, 1.0],
        "eps_Z2": -1.0,
        "T_plus_munu_values": [
            [[2.0, 0.0], [0.0, 3.0]],
            [[4.0, 0.0], [0.0, 5.0]],
        ],
        "T_minus_munu_values": [
            [[1.0, 0.0], [0.0, 7.0]],
            [[2.0, 0.0], [0.0, 11.0]],
        ],
        "tangent_vectors_values": [
            [[1.0, 0.0], [0.0, 1.0]],
            [[1.0, 0.0], [0.0, 1.0]],
        ],
        "normal_plus_values": [[1.0, 0.0], [1.0, 0.0]],
        "normal_minus_values": [[1.0, 0.0], [1.0, 0.0]],
        "radial_variation_tangent_weights": [[1.0, 0.0], [0.5, 0.0]],
    }
    payload.update(overrides)
    return payload


class MatterFluxActiveProjectionRadialInputWriterGateTests(unittest.TestCase):
    def test_computes_active_projection_and_radial_reduction(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source_path = root / "source.json"
            output_path = root / "out.json"
            source_path.write_text(json.dumps(_source()), encoding="utf-8")

            payload = build_payload(input_path=source_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["active_flux_projection_ready"])
        self.assertEqual(written["selected_route"], "active_projection")
        self.assertEqual(written["F_Z2Sigma_tangent_values"], [[1.0, 0.0], [2.0, 0.0]])
        self.assertEqual(written["E_matterFlux_values"], [1.0, 1.0])

    def test_forbidden_z4_reuse_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source_path = root / "source.json"
            source_path.write_text(
                json.dumps(_source(archived_z4_reuse_used=True)),
                encoding="utf-8",
            )

            payload = build_payload(input_path=source_path, output_path=root / "out.json")

        self.assertFalse(payload["gate_passed"])
        self.assertIn("Forbidden provenance", payload["validation_error"])

    def test_missing_input_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "active_matter_flux_projection_components")


if __name__ == "__main__":
    unittest.main()
