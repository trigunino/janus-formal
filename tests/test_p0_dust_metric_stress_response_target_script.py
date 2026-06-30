from __future__ import annotations

import unittest

from scripts.build_p0_dust_metric_stress_response_target import build_payload


class P0DustMetricStressResponseTargetTests(unittest.TestCase):
    def test_dust_chain_rule_closed_but_action_response_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dust-chain-rule-closed-action-response-open")
        self.assertTrue(payload["dust_chain_rule_closed"])
        self.assertTrue(payload["normalization_projection_closed"])
        self.assertTrue(payload["fixed_current_density_response_available"])
        self.assertTrue(payload["fixed_pullback_delta_t_branch_available"])
        self.assertFalse(payload["density_response_closed"])
        self.assertFalse(payload["transverse_velocity_response_closed"])
        self.assertFalse(payload["pulled_dust_response_closed"])
        self.assertFalse(payload["full_dust_delta_g_t_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_identities_include_chain_rule_and_normalization_projection(self) -> None:
        text = " ".join(row["formula"] for row in build_payload()["identities"])

        self.assertIn("delta_g T^{mu nu}", text)
        self.assertIn("delta_g rho", text)
        self.assertIn("delta_g u^mu", text)
        self.assertIn("u_mu delta_g u^mu", text)
        self.assertIn("delta g_{mu nu}", text)

    def test_closure_requirements_keep_dust_action_and_pullback_explicit(self) -> None:
        requirements = " ".join(build_payload()["closure_requirements"])

        self.assertIn("dust action", requirements)
        self.assertIn("conserved current", requirements)
        self.assertIn("transverse delta_g u", requirements)
        self.assertIn("transported/pulled dust", requirements)


if __name__ == "__main__":
    unittest.main()
