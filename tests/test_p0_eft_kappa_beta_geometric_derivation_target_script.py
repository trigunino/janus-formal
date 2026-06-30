from __future__ import annotations

import unittest

from scripts.build_p0_eft_kappa_beta_geometric_derivation_target import build_payload, render_markdown


class P0EFTKappaBetaGeometricDerivationTargetTests(unittest.TestCase):
    def test_kappa_and_beta_targets_are_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["kappa_derivation_target_encoded"])
        self.assertTrue(status["beta_derivation_target_encoded"])
        self.assertFalse(status["kappa_geometrically_derived"])
        self.assertFalse(status["beta_geometrically_derived"])
        self.assertFalse(status["prediction_ready"])

    def test_beta_denominator_risk_is_recorded(self) -> None:
        payload = build_payload()

        self.assertIn("1/Delta_chi", payload["verdict"])
        self.assertIn("Delta_chi denominator", " ".join(payload["obligations"]))

    def test_targets_match_run1_solution(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["kappa"]["target"], "kappa = 2*q_A*Delta_chi")
        self.assertEqual(payload["beta"]["target"], "beta = -sigma*(1+tau)/(2*Delta_chi)")

    def test_markdown_keeps_ready_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("run1_pure_geometric_closure: False", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
