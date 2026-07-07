import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_chi_ll_will_action_power_selection_gate import (
    build_payload,
)


class ChiLLWillActionPowerSelectionGateTests(unittest.TestCase):
    def test_default_selects_will_power_but_blocks_normalization(self):
        payload = build_payload(Path("missing-will-inputs.json"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["WILL_power_selection_ready"])
        self.assertFalse(payload["single_micro_relation_ready"])
        self.assertEqual(payload["will_conditions"]["power_p_value"], 0.5)
        self.assertIn("derive_worldvolume_charge_unit_q_LL", payload["blocked_by"])

    def test_will_power_fixes_lambda_over_q_when_area_flux_inputs_exist(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "will.json"
            path.write_text(
                json.dumps(
                    {
                        "flux_integer_n": 1,
                        "N_gap": 1,
                        "A_gap_m2": 4.0 * math.pi,
                        "area_gauge": "physical_induced_S2_metric",
                        "non_observational_provenance": True,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertTrue(payload["single_micro_relation_ready"])
        self.assertAlmostEqual(payload["C_area_m_minus_4"], 0.5)
        self.assertAlmostEqual(
            payload["predicted_lambda_F2_over_q_LL"],
            1.0 / (4.0 * math.sqrt(0.5)),
        )
        self.assertFalse(payload["chi_LL_prediction_ready"])

    def test_q_route_predicts_lambda_for_will_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "will.json"
            path.write_text(
                json.dumps(
                    {
                        "flux_integer_n": 1,
                        "N_gap": 1,
                        "A_gap_m2": 4.0 * math.pi,
                        "q_LL_dimensionless": 2.0,
                        "area_gauge": "physical_induced_S2_metric",
                        "non_observational_provenance": True,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertTrue(payload["q_LL_route_predicts_lambda_F2"])
        self.assertAlmostEqual(
            payload["predicted_lambda_F2_if_q_LL_given"],
            2.0 / (4.0 * math.sqrt(0.5)),
        )
        self.assertAlmostEqual(payload["predicted_F2_0_m_minus_4_if_q_LL_given"], 0.125)


if __name__ == "__main__":
    unittest.main()
