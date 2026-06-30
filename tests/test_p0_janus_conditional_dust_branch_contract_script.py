from __future__ import annotations

import unittest

from scripts.build_p0_janus_conditional_dust_branch_contract import build_payload, render_markdown


class P0JanusConditionalDustBranchContractTests(unittest.TestCase):
    def test_required_conditions_are_explicit(self) -> None:
        conditions = " ".join(build_payload()["required_conditions"])

        self.assertIn("p_plus=p_minus=0", conditions)
        self.assertIn("Pi_plus", conditions)
        self.assertIn("B_4vol exactly once", conditions)
        self.assertIn("denominators are nonzero", conditions)

    def test_diagnostic_ready_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["dust_conditions_explicit"])
        self.assertTrue(payload["dust_branch_diagnostic_ready"])
        self.assertFalse(payload["dust_branch_general_physics_ready"])
        self.assertFalse(payload["residuals_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_forbidden_outputs_block_overclaim(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_outputs"])

        self.assertIn("general perfect-fluid closure", forbidden)
        self.assertIn("anisotropic-stress closure", forbidden)
        self.assertIn("sigma8/S8", forbidden)

    def test_no_fit(self) -> None:
        self.assertFalse(build_payload()["uses_observational_fit"])

    def test_markdown_reports_contract(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Dust branch diagnostic ready: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
