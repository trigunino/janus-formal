from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_conditional_closure_theorem import build_payload, render_markdown


class P0StueckelbergConditionalClosureTheoremTests(unittest.TestCase):
    def test_theorem_is_conditional_not_prediction_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["conditional_closure_proved"])
        self.assertFalse(status["unconditional_closure_proved"])
        self.assertFalse(status["source_derived"])
        self.assertTrue(status["new_axiom"])
        self.assertFalse(status["physics_closed"])
        self.assertFalse(status["prediction_ready"])

    def test_assumptions_require_two_sector_covariance_and_map_eom(self) -> None:
        assumptions = " ".join(row["statement"] for row in build_payload()["assumptions"])

        self.assertIn("plus-sector diffeomorphisms", assumptions)
        self.assertIn("minus-sector diffeomorphisms", assumptions)
        self.assertIn("E_phi=0 and E_L=0", assumptions)
        self.assertIn("same phi/L data", assumptions)

    def test_split_identities_close_both_residuals_on_shell(self) -> None:
        identities = " ".join(
            row["off_shell_identity"] + " " + row["on_shell_result"]
            for row in build_payload()["split_identities"]
        )

        self.assertIn("R_plus_nu=0", identities)
        self.assertIn("R_minus_nu=0", identities)
        self.assertIn("E_phi", identities)
        self.assertIn("E_L", identities)

    def test_markdown_records_new_axiom_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("conditional_closure_proved: True", markdown)
        self.assertIn("source_derived: False", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
