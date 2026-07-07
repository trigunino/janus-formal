import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_area_superselection_sector_manifest import (
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
        "superselection_sector_law_declared": True,
        "N_gap_sectors": [1, 2, 4],
        "holst_immirzi_abs": 2.0,
        "j_min": 0.5,
        "provenance": "active_sigma_area_superselection",
    }


class SigmaAreaSuperselectionSectorManifestTests(unittest.TestCase):
    def test_missing_inputs_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(Path(tmp) / "missing.json")

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["superselection_family_ready"])
        self.assertIn("superselection_sector_law_declared", payload["blocked_by"])

    def test_valid_family_outputs_discrete_sector_table(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(valid_input()), encoding="utf-8")
            payload = build_payload(path)

        lp2 = HBAR_SI * G_SI / C_SI**3
        expected_gap = 8.0 * math.pi * 2.0 * lp2 * math.sqrt(0.5 * 1.5)
        self.assertTrue(payload["superselection_family_ready"])
        self.assertFalse(payload["unique_prediction_ready"])
        self.assertEqual(payload["N_gap_sectors"], [1, 2, 4])
        self.assertAlmostEqual(payload["A_gap_m2"], expected_gap)
        self.assertEqual(payload["sector_table"][0]["N_gap"], 1)

    def test_single_sector_can_write_area_spectrum_input(self):
        data = valid_input()
        data["N_gap_sectors"] = [3]
        with tempfile.TemporaryDirectory() as tmp:
            inp = Path(tmp) / "inputs.json"
            out = Path(tmp) / "area.json"
            inp.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(inp, out, write_output=True)

            self.assertTrue(out.exists())
            written = json.loads(out.read_text(encoding="utf-8"))

        self.assertTrue(payload["superselection_family_ready"])
        self.assertEqual(written["N_gap"], 3)

    def test_observational_provenance_rejected(self):
        data = valid_input()
        data["provenance"] = "fit_bao"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inputs.json"
            path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(path)

        self.assertFalse(payload["superselection_family_ready"])
        self.assertIn("non_observational_provenance", payload["blocked_by"])


if __name__ == "__main__":
    unittest.main()
