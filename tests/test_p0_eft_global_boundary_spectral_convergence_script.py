from __future__ import annotations

import unittest

from scripts.build_p0_eft_global_boundary_spectral_convergence import build_payload, render_markdown


class P0EFTGlobalBoundarySpectralConvergenceTests(unittest.TestCase):
    def test_global_status_is_conditional_not_unconditional(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["beta_response_ratio_accepted"])
        self.assertTrue(status["run1_conditionally_closed"])
        self.assertTrue(status["run2_conditionally_closed"])
        self.assertTrue(status["prediction_ready_conditional"])
        self.assertFalse(status["prediction_ready_unconditional"])

    def test_run1_and_run2_outputs_are_present(self) -> None:
        payload = build_payload()

        self.assertIn("P_chiral", payload["run1"]["local_projector"])
        self.assertEqual(payload["run2"]["eta_mod2"], "0 conditionally")

    def test_conditions_keep_assumptions_explicit(self) -> None:
        conditions = " ".join(build_payload()["conditions"])

        self.assertIn("compact Riemannian APS boundary", conditions)
        self.assertIn("beta is accepted as a Cartan-GHY response ratio", conditions)

    def test_markdown_reports_conditional_ready(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("prediction_ready_conditional: True", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
