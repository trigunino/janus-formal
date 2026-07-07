import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_chi_ll_area_gap_exit_gate import build_payload


class ChiLLAreaGapExitGateTests(unittest.TestCase):
    def test_default_blocks_without_area_inputs(self):
        payload = build_payload(Path("missing-area-gap.json"))

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["area_gap_exit_ready"])
        self.assertIn("quantum_area_operator_on_Sigma", payload["blocked_by"])
        self.assertIn("A_gap_m2", payload["blocked_by"])

    def test_conditional_closure_with_area_gap_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "area.json"
            path.write_text(
                json.dumps(
                    {
                        "quantum_area_operator_on_Sigma": True,
                        "A_gap_m2": 16.0 * math.pi,
                        "A_Sigma_equals_N_gap_A_gap_theorem": True,
                        "N_gap": 1,
                        "area_gauge": "physical_induced_S2_metric",
                        "non_observational_provenance": True,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertTrue(payload["area_gap_exit_ready"])
        self.assertAlmostEqual(payload["derivation"]["R_s_m"], 2.0)


if __name__ == "__main__":
    unittest.main()
