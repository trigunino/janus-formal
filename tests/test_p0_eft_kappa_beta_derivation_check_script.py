from __future__ import annotations

import unittest

from scripts.build_p0_eft_kappa_beta_derivation_check import build_payload, render_markdown


class P0EFTKappaBetaDerivationCheckTests(unittest.TestCase):
    def test_kappa_closes_conditionally(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["kappa_geometrically_closed_conditionally"])
        self.assertIn("2*q_A*Delta_chi", build_payload()["kappa"]["coefficient"])

    def test_beta_is_ratio_not_constant(self) -> None:
        payload = build_payload()
        status = payload["theorem_status"]

        self.assertTrue(status["beta_flux_ratio_closed_conditionally"])
        self.assertFalse(status["beta_as_constant_geometrically_derived"])
        self.assertIn("response coefficient", payload["beta"]["denominator_status"])

    def test_prediction_remains_false_until_beta_choice(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run1_pure_geometric_closure_if_beta_ratio_allowed"])
        self.assertFalse(status["prediction_ready"])

    def test_markdown_names_choice(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("beta may be treated as a boundary response ratio", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
