import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_cover_measure_transport_from_sigma_metrics import (
    build_payload,
)


def _source() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "a_grid": [1.0],
        "metric_plus_munu_values": [[[-1.0, 0.0], [0.0, 4.0]]],
        "metric_minus_munu_values": [[[-1.0, 0.0], [0.0, 9.0]]],
    }


class JanusZ2CoverMeasureTransportFromSigmaMetricsScriptTest(unittest.TestCase):
    def test_writes_cover_measure_inputs_from_sigma_metrics(self):
        with tempfile.TemporaryDirectory() as tmp:
            input_path = Path(tmp) / "sigma_metrics.json"
            output_path = Path(tmp) / "measure_inputs.json"
            input_path.write_text(json.dumps(_source()), encoding="utf-8")
            payload = build_payload(input_path, output_path)
            written = json.loads(output_path.read_text(encoding="utf-8"))
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["local_sigma_restriction_only"])
        self.assertEqual(written["sqrt_abs_g_plus"], [2.0])
        self.assertAlmostEqual(written["sqrt_abs_g_minus"][0], 3.0)


if __name__ == "__main__":
    unittest.main()
