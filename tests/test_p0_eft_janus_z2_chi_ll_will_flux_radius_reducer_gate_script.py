import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_chi_ll_will_flux_radius_reducer_gate import (
    build_payload,
)


class ChiLLWillFluxRadiusReducerGateTests(unittest.TestCase):
    def test_default_blocks_without_ratio(self):
        payload = build_payload(Path("missing-will-radius.json"))

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["WILL_flux_radius_ready"])
        self.assertIn("lambda_F2_over_q_LL_available", payload["blocked_by"])

    def test_ratio_and_flux_integer_predict_radius(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "will_radius.json"
            path.write_text(
                json.dumps(
                    {
                        "flux_integer_n": 2,
                        "lambda_F2_over_q_LL": 0.5,
                        "area_gauge": "physical_induced_S2_metric",
                        "non_observational_provenance": True,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        expected_rs = (8.0 * 4.0 * 0.25) ** 0.25
        self.assertTrue(payload["WILL_flux_radius_ready"])
        self.assertAlmostEqual(payload["R_s_m_if_ratio_dimension_m_minus_2"], expected_rs)
        self.assertAlmostEqual(
            payload["chi_LL_abs_inverse_m"],
            1.0 / (8.0 * math.pi * expected_rs),
        )


if __name__ == "__main__":
    unittest.main()
