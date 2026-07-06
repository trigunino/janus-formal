import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_sigma_surface_hk_isotropic_geometry import build_payload


def _k_grid() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": [0.25, 0.5],
        "K_s_plus_Z2Sigma": [3.0, 6.0],
        "K_s_minus_Z2Sigma": [1.0, 2.0],
        "K_tau_plus_Z2Sigma": [5.0, 10.0],
        "K_tau_minus_Z2Sigma": [2.0, 4.0],
        "z2_orientation_sign": -1.0,
        "K_provenance": "active tunnel embedding extrinsic curvature grid",
    }


class JanusZ2SigmaSurfaceHKIsotropicGeometryScriptTest(unittest.TestCase):
    def test_missing_k_grid_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                output_path=Path(tmp) / "geometry.json",
            )
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "flrw_extrinsic_curvature_grid_missing")

    def test_writes_oriented_surface_hk_geometry(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "k_grid.json"
            output_path = Path(tmp) / "geometry.json"
            input_path.write_text(json.dumps(_k_grid()), encoding="utf-8")
            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["K_s"], [2.0, 4.0])
        self.assertEqual(written["K_tau"], [3.0, 6.0])
        self.assertEqual(written["sigma_orientation_minus"], [-1.0, -1.0])


if __name__ == "__main__":
    unittest.main()
