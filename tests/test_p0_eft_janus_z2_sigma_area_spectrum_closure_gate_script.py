import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_area_spectrum_closure_gate import (
    C_SI,
    G_SI,
    HBAR_SI,
    build_payload,
)


def valid_input() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "source": "active_derived",
        "area_operator_on_Sigma_derived": True,
        "Holst_area_spectrum_law_derived": True,
        "area_gauge": "physical_induced_S2_metric",
        "area_spectrum_provenance": "active_holst_sigma_area_operator",
        "holst_immirzi_abs": 2.0,
        "j_min": 0.5,
        "N_gap": 3,
    }


class SigmaAreaSpectrumClosureGateTests(unittest.TestCase):
    def test_default_blocks_without_inputs(self):
        payload = build_payload(Path("missing-area-spectrum.json"))

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["area_gap_formula_ready"])
        self.assertIn("area_operator_on_Sigma_derived", payload["blocked_by"])

    def test_valid_inputs_compute_area_gap_and_radius(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "area_spectrum.json"
            path.write_text(json.dumps(valid_input()), encoding="utf-8")
            payload = build_payload(path)

        lp2 = HBAR_SI * G_SI / C_SI**3
        expected_gap = 8.0 * math.pi * 2.0 * lp2 * math.sqrt(0.5 * 1.5)
        expected_radius = math.sqrt(3.0 * expected_gap / (4.0 * math.pi))
        self.assertTrue(payload["area_gap_formula_ready"])
        self.assertTrue(payload["R_s_prediction_ready"])
        self.assertAlmostEqual(payload["derivation"]["A_gap_m2"], expected_gap)
        self.assertAlmostEqual(payload["derivation"]["R_s_m"], expected_radius)

    def test_without_N_gap_only_area_gap_is_ready(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "area_spectrum.json"
            data = valid_input()
            data.pop("N_gap")
            path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(path)

        self.assertTrue(payload["area_gap_formula_ready"])
        self.assertFalse(payload["R_s_prediction_ready"])
        self.assertIn("positive_integer_N_gap", payload["blocked_by"])

    def test_writes_area_gap_payload_for_existing_gate(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            input_path = base / "area_spectrum.json"
            output_path = base / "area_gap.json"
            input_path.write_text(json.dumps(valid_input()), encoding="utf-8")
            payload = build_payload(input_path, output_path, write_output=True)

            self.assertTrue(output_path.exists())
            out = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["R_s_prediction_ready"])
        self.assertTrue(out["quantum_area_operator_on_Sigma"])
        self.assertEqual(out["N_gap"], 3)


if __name__ == "__main__":
    unittest.main()
