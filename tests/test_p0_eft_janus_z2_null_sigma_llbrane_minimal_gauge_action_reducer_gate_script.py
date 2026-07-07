import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_minimal_gauge_action_reducer_gate import (
    build_payload,
)


def base_payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "source": "active_derived",
        "a0_matching_value": 0.125,
        "action_provenance": "active_llbrane_gauge_action_certificate",
        "observational_fit_used": False,
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
    }


class LLBraneMinimalGaugeActionReducerGateTests(unittest.TestCase):
    def test_missing_action_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(input_path=Path(tmp) / "missing.json")

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["dimensionful_F2_0_ready"])

    def test_sqrt_action_only_gives_auxiliary_units(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "action.json"
            data = base_payload()
            data["L_F2_family"] = "sqrt_F2_unit_normalized"
            path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(input_path=path)

        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["computed"]["F2_0_auxiliary_units"], 1.0 / 16.0)
        self.assertIsNone(payload["computed"]["F2_0_m_minus_4"])

    def test_dimensionful_monomial_can_reduce_F2(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "action.json"
            data = base_payload()
            data.update(
                {
                    "L_F2_family": "monomial_lambda_F2_power_p",
                    "lambda_F2": 0.25,
                    "power_p": 1.0,
                    "F2_units": "m_minus_4",
                }
            )
            path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(input_path=path)

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["dimensionful_F2_0_ready"])
        self.assertEqual(payload["computed"]["F2_0_m_minus_4"], 0.5)


if __name__ == "__main__":
    unittest.main()
