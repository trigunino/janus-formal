import json
import tempfile
import unittest
from pathlib import Path

from scripts.derive_p0_eft_janus_z2_cover_measure_transport import build_payload


def _payload() -> dict:
    return {
        "active_core": "JanusZ2CoverMasterAction",
        "source": "active_cover_metric_determinants",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "rho_eff_shortcut_used": False,
        "negative_thermodynamic_density_postulated": False,
        "full_no_fit_prediction_ready": False,
        "parameter_grid": [0.5, 1.0],
        "sqrt_abs_g_plus": [2.0, 4.0],
        "sqrt_abs_g_minus": [6.0, 2.0],
        "tau_jacobian_abs_minus_to_plus": [1.0, 2.0],
        "tau_jacobian_abs_plus_to_minus": [1.0, 0.5],
    }


class JanusZ2CoverMeasureTransportScriptTest(unittest.TestCase):
    def test_blocks_without_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(Path(tmp) / "missing.json", Path(tmp) / "out.json")
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "measure_transport_inputs_missing")

    def test_writes_measure_transport(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "in.json"
            output_path = Path(tmp) / "out.json"
            input_path.write_text(json.dumps(_payload()), encoding="utf-8")
            payload = build_payload(input_path, output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["measure_transport_ready"])
        self.assertEqual(written["B_minus_to_plus"], [3.0, 1.0])


if __name__ == "__main__":
    unittest.main()
