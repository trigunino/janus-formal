import json
import tempfile
import unittest
from pathlib import Path

from scripts.derive_p0_eft_janus_z2_cover_sigma_source_from_alpha_h import build_payload


def _manifest() -> dict:
    return {
        "active_core": "JanusZ2CoverMasterAction",
        "source": "master_boundary_variation_alpha_h",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "rho_eff_shortcut_used": False,
        "negative_thermodynamic_density_postulated": False,
        "two_independent_actions_used": False,
        "full_no_fit_prediction_ready": False,
        "parameter_grid": [1.0],
        "alpha_h_tau": [2.0],
        "alpha_h_s": [3.0],
        "sigma_orientation_plus": [1.0],
        "sigma_orientation_minus": [-1.0],
    }


class JanusZ2CoverSigmaSourceFromAlphaHScriptTest(unittest.TestCase):
    def test_blocks_without_alpha_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(Path(tmp) / "missing.json", Path(tmp) / "out.json")
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "sigma_alpha_h_inputs_missing")

    def test_writes_sigma_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "alpha.json"
            output_path = Path(tmp) / "sigma.json"
            input_path.write_text(json.dumps(_manifest()), encoding="utf-8")
            payload = build_payload(input_path, output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["sigma_source_ready"])
        self.assertEqual(written["J_Sigma_plus_tau"], [-4.0])


if __name__ == "__main__":
    unittest.main()
