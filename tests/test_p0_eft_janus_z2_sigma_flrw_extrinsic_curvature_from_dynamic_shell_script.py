import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_from_dynamic_shell import (
    build_payload,
)


def _dynamic_shell() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_fit_used": False,
        "a_grid": [0.5, 1.0],
        "R_Sigma_of_a": [2.0, 4.0],
        "R_dot_of_a": [0.0, 0.0],
        "R_ddot_of_a": [0.0, 0.0],
        "f_plus_of_R": [4.0, 9.0],
        "f_minus_of_R": [1.0, 4.0],
        "df_plus_dR": [2.0, 4.0],
        "df_minus_dR": [1.0, 2.0],
        "epsilon_plus": 1.0,
        "epsilon_minus": -1.0,
        "z2_orientation_sign": -1.0,
        "dynamic_shell_provenance": "active dynamic shell embedding functions",
    }


class JanusZ2SigmaFLRWExtrinsicCurvatureFromDynamicShellScriptTest(unittest.TestCase):
    def test_missing_input_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                input_path=Path(tmp) / "missing.json",
                output_path=Path(tmp) / "out.json",
            )
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "dynamic_shell_extrinsic_curvature_inputs_missing")

    def test_writes_k_grid_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            input_path = root / "dynamic.json"
            output_path = root / "k_grid_inputs.json"
            input_path.write_text(json.dumps(_dynamic_shell()), encoding="utf-8")
            payload = build_payload(input_path=input_path, output_path=output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(written["K_s_plus_Z2Sigma"], [1.0, 0.75])
        self.assertEqual(written["K_s_minus_Z2Sigma"], [-0.5, -0.5])
        self.assertEqual(written["K_tau_plus_Z2Sigma"], [0.5, 2.0 / 3.0])
        self.assertEqual(written["K_tau_minus_Z2Sigma"], [-0.5, -0.5])
        self.assertEqual(written["K_reduction_route"], "dynamic_spherical_shell")


if __name__ == "__main__":
    unittest.main()
