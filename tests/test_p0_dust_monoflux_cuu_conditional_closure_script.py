from __future__ import annotations

import unittest

from scripts.build_p0_dust_monoflux_cuu_conditional_closure import build_payload, render_markdown


class P0DustMonofluxCuuConditionalClosureTests(unittest.TestCase):
    def test_projected_residual_closes_after_substitution(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dust-monoflux-cuu-conditional-closure")
        self.assertEqual(payload["projected_residual"], ["0", "0"])
        self.assertTrue(payload["residual_zero_after_substitution"])
        self.assertTrue(payload["conditional_cuu_closure"])
        self.assertFalse(payload["prediction_ready"])

    def test_conditions_keep_branch_and_action_limits(self) -> None:
        payload = build_payload()
        conditions = " ".join(payload["closure_conditions"])
        still_open = " ".join(payload["still_open"])

        self.assertIn("cold monoflux dust", conditions)
        self.assertIn("E_alpha=rho C_alpha", conditions)
        self.assertIn("same phi/L/B4vol", conditions)
        self.assertIn("derive E_alpha", still_open)
        self.assertIn("D L and D log B4vol", still_open)

    def test_not_promoted_to_full_physics(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["dust_monoflux_branch_required"])
        self.assertFalse(payload["action_derivation_supplied"])
        self.assertFalse(payload["same_phi_l_dynamically_selected"])
        self.assertFalse(payload["dl_dlogb_residuals_closed"])
        self.assertFalse(payload["mirror_residuals_closed"])
        self.assertFalse(payload["physics_closed"])

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Residual zero after substitution: True", markdown)
        self.assertIn("Action derivation supplied: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
