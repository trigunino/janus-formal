import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_bimetric_bulk_to_sigma_flux_input_assembler import (
    build_payload,
)


class BimetricBulkToSigmaFluxInputAssemblerTests(unittest.TestCase):
    def test_blocks_without_three_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = build_payload(
                fluid_path=root / "fluid.json",
                embedding_path=root / "embedding.json",
                radial_weights_path=root / "radial.json",
                output_path=root / "out.json",
            )
        self.assertFalse(payload["gate_passed"])
        self.assertIn("missing_sector_perfect_fluid_on_sigma_inputs", payload["blocked_by"])

    def test_assembles_complete_runner_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fluid = root / "fluid.json"
            embedding = root / "embedding.json"
            radial = root / "radial.json"
            out = root / "out.json"
            base = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
                "archived_z4_background_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
            }
            fluid.write_text(
                json.dumps(
                    {
                        **base,
                        "a_grid": [1.0, 2.0],
                        "rho_plus_values": [2.0, 2.0],
                        "p_plus_values": [0.0, 0.0],
                        "rho_minus_values": [-1.0, -1.0],
                        "p_minus_values": [0.0, 0.0],
                        "metric_plus_munu_values": [[[-1.0, 0.0], [0.0, 1.0]]] * 2,
                        "metric_minus_munu_values": [[[-1.0, 0.0], [0.0, 1.0]]] * 2,
                        "u_plus_contravariant_values": [[1.0, 0.0]] * 2,
                        "u_minus_contravariant_values": [[1.0, 0.0]] * 2,
                    }
                ),
                encoding="utf-8",
            )
            embedding.write_text(
                json.dumps(
                    {
                        **base,
                        "a_grid": [1.0, 2.0],
                        "tangent_frames_plus": [[[1.0, 0.0]], [[1.0, 0.0]]],
                        "unit_normals_plus": [[0.0, 1.0], [0.0, 1.0]],
                        "unit_normals_minus": [[0.0, -1.0], [0.0, -1.0]],
                        "z2_orientation_sign": -1.0,
                    }
                ),
                encoding="utf-8",
            )
            radial.write_text(
                json.dumps(
                    {
                        **base,
                        "a_grid": [1.0, 2.0],
                        "radial_variation_tangent_weights": [[1.0], [1.0]],
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(
                fluid_path=fluid,
                embedding_path=embedding,
                radial_weights_path=radial,
                output_path=out,
            )
            written = json.loads(out.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["rho_minus_values"], [-1.0, -1.0])
        self.assertEqual(written["eps_Z2"], -1.0)


if __name__ == "__main__":
    unittest.main()
