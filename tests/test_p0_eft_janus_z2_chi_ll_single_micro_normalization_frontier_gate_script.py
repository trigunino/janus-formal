import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_chi_ll_single_micro_normalization_frontier_gate import (
    build_payload,
)


class ChiLLSingleMicroNormalizationFrontierTests(unittest.TestCase):
    def test_default_blocks_without_required_inputs(self):
        payload = build_payload(Path("missing-single-micro.json"))

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["single_micro_relation_ready"])
        self.assertIn("flux_integer_n_available", payload["blocked_by"])

    def test_q_route_predicts_lambda(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "single_micro.json"
            path.write_text(
                json.dumps(
                    {
                        "flux_integer_n": 1,
                        "N_gap": 1,
                        "A_gap_m2": 4.0 * math.pi,
                        "power_p": 2.0,
                        "q_LL_dimensionless": 2.0,
                        "area_gauge": "physical_induced_S2_metric",
                        "non_observational_provenance": True,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertTrue(payload["single_micro_relation_ready"])
        self.assertTrue(payload["q_LL_route_predicts_lambda_F2"])
        self.assertAlmostEqual(payload["C_area_m_minus_4"], 0.5)
        self.assertAlmostEqual(payload["invariant_lambda_F2_over_q_LL_2p"], 0.25)
        self.assertAlmostEqual(payload["predicted_F2_0_m_minus_4_if_q_LL_given"], 0.125)
        self.assertAlmostEqual(payload["predicted_lambda_F2_if_q_LL_given"], 4.0)

    def test_lambda_route_predicts_q(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "single_micro.json"
            path.write_text(
                json.dumps(
                    {
                        "flux_integer_n": 1,
                        "N_gap": 1,
                        "A_gap_m2": 4.0 * math.pi,
                        "power_p": 2.0,
                        "lambda_F2": 4.0,
                        "area_gauge": "physical_induced_S2_metric",
                        "non_observational_provenance": True,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertTrue(payload["single_micro_relation_ready"])
        self.assertTrue(payload["lambda_F2_route_predicts_q_LL"])
        self.assertAlmostEqual(payload["predicted_F2_0_m_minus_4_if_lambda_F2_given"], 0.125)
        self.assertAlmostEqual(payload["predicted_q_LL_if_lambda_F2_given"], 2.0)

    def test_pair_consistency_when_both_micro_inputs_are_given(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "single_micro.json"
            path.write_text(
                json.dumps(
                    {
                        "flux_integer_n": 1,
                        "N_gap": 1,
                        "A_gap_m2": 4.0 * math.pi,
                        "power_p": 2.0,
                        "q_LL_dimensionless": 2.0,
                        "lambda_F2": 4.0,
                        "area_gauge": "physical_induced_S2_metric",
                        "non_observational_provenance": True,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertTrue(payload["both_micro_inputs_consistent"])
        self.assertTrue(payload["pair_consistency"]["compatible"])
        self.assertAlmostEqual(
            payload["pair_consistency"]["F2_from_lambda_F2"],
            payload["pair_consistency"]["F2_from_q_LL"],
        )


if __name__ == "__main__":
    unittest.main()
