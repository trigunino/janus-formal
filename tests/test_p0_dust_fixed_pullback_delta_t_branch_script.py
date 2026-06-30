from __future__ import annotations

import unittest

from scripts.build_p0_dust_fixed_pullback_delta_t_branch import build_payload


class P0DustFixedPullbackDeltaTBranchTests(unittest.TestCase):
    def test_conditional_delta_t_closed_but_action_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "conditional-dust-delta-t-closed-action-open")
        self.assertTrue(payload["fixed_phi_source_branch_closed"])
        self.assertTrue(payload["density_response_closed_under_branch"])
        self.assertTrue(payload["velocity_response_closed_under_branch"])
        self.assertTrue(payload["dust_delta_g_t_closed_under_branch"])
        self.assertFalse(payload["janus_action_delta_g_t_closed"])
        self.assertFalse(payload["full_k_variation_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_contain_density_velocity_and_stress_response(self) -> None:
        text = " ".join(row["formula"] + row["status"] for row in build_payload()["branch_rows"])

        self.assertIn("rho_eff=B_4vol rho_to", text)
        self.assertIn("delta_g rho_eff", text)
        self.assertIn("delta_g u^mu", text)
        self.assertIn("delta_g T^{mu nu}", text)
        self.assertIn("open-action-required", text)


if __name__ == "__main__":
    unittest.main()
