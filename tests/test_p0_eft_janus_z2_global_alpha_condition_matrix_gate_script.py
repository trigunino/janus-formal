import unittest

from scripts.build_p0_eft_janus_z2_global_alpha_condition_matrix_gate import build_payload


class GlobalAlphaConditionMatrixGateTests(unittest.TestCase):
    def test_condition_matrix_selects_best_routes_without_generating_alpha(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["alpha_generated_now"])
        self.assertEqual(payload["best_discrete_route"], "PT_monodromy_identity")
        self.assertEqual(payload["best_continuous_route"], "janus_vacuum_minimum")

    def test_no_candidate_currently_quantizes_alpha(self):
        payload = build_payload()

        self.assertTrue(all(not row["can_quantize_alpha"] for row in payload["candidates"]))


if __name__ == "__main__":
    unittest.main()
