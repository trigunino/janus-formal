from __future__ import annotations

import unittest

from scripts.build_p0_pulled_m_metric_response_target import build_payload


class P0PulledMMetricResponseTargetTests(unittest.TestCase):
    def test_chain_rule_closed_but_l_law_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "pulled-m-chain-rule-closed-l-law-open")
        self.assertTrue(payload["m_chain_rule_closed"])
        self.assertTrue(payload["fixed_minus_source_branch_closed"])
        self.assertTrue(payload["free_l_branch_available"])
        self.assertTrue(payload["metric_compatible_l_branch_available"])
        self.assertTrue(payload["l_metric_response_law_target_available"])
        self.assertTrue(payload["pulled_m_symmetric_l_substitution_available"])
        self.assertFalse(payload["solder_metric_response_closed"])
        self.assertFalse(payload["pulled_m_metric_response_closed"])
        self.assertFalse(payload["full_k_plus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_chain_rule_fixed_source_and_l_branches(self) -> None:
        text = " ".join(row["formula"] + row["status"] for row in build_payload()["response_rows"])

        self.assertIn("delta_g M", text)
        self.assertIn("delta_g L_mu", text)
        self.assertIn("delta_{g_plus} T_minus", text)
        self.assertIn("L^T g_plus", text)
        self.assertIn("delta_{g_plus} L=0", text)
        self.assertIn("tetrads", text)


if __name__ == "__main__":
    unittest.main()
