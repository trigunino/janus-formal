import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_chi_ll_area_flux_micro_parameter_constraint import (
    build_payload,
)


class ChiLLAreaFluxMicroParameterConstraintTests(unittest.TestCase):
    def test_default_blocks_without_inputs(self):
        payload = build_payload(Path("missing-micro.json"))

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["micro_parameter_relation_ready"])
        self.assertIn("flux_integer_n_available", payload["blocked_by"])

    def test_relation_predicts_f2_if_q_is_given(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "micro.json"
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

        rhs = 0.5
        self.assertTrue(payload["micro_parameter_relation_ready"])
        self.assertAlmostEqual(payload["constraint_rhs_m_minus_4"], rhs)
        self.assertAlmostEqual(payload["predicted_F2_0_m_minus_4_if_q_LL_given"], rhs / 4.0)

    def test_relation_predicts_q_if_f2_is_given(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "micro.json"
            path.write_text(
                json.dumps(
                    {
                        "flux_integer_n": 1,
                        "N_gap": 1,
                        "A_gap_m2": 4.0 * math.pi,
                        "F2_0_m_minus_4": 0.125,
                        "area_gauge": "physical_induced_S2_metric",
                        "non_observational_provenance": True,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertTrue(payload["micro_parameter_relation_ready"])
        self.assertAlmostEqual(payload["predicted_q_LL_if_F2_0_given"], 2.0)


if __name__ == "__main__":
    unittest.main()
