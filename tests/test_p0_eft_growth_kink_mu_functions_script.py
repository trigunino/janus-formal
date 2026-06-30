from __future__ import annotations

import unittest

from scripts.build_p0_eft_growth_kink_mu_functions import build_payload, render_markdown


class P0EFTGrowthKinkMuFunctionsTests(unittest.TestCase):
    def test_growth_functions_are_partial(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["skink_formula_encoded"])
        self.assertFalse(status["skink_coefficient_derived"])
        self.assertTrue(status["mu_form_encoded"])
        self.assertTrue(status["M_eff2_conditionally_closed"])
        self.assertFalse(status["alpha_Janus_derived"])
        self.assertFalse(status["fsigma8_prediction_ready"])

    def test_mu_uses_meff_gap_and_alpha_open(self) -> None:
        mu = build_payload()["mu"]

        self.assertIn("3*H(a)^2/2", mu["M_eff2"])
        self.assertIn("active stress", mu["alpha_Janus"])

    def test_solver_jump_is_continuous_delta(self) -> None:
        solver = build_payload()["solver"]

        self.assertIn("delta continuous", solver["jump"])
        self.assertIn("delta' receives S_kink", solver["jump"])

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("alpha_Janus_derived: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
