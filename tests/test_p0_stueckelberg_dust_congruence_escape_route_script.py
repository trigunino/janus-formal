from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_dust_congruence_escape_route import build_payload, render_markdown


class P0StueckelbergDustCongruenceEscapeRouteTests(unittest.TestCase):
    def test_route_reduces_overconstraint_but_not_full_closure(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dust-congruence-route-conditional")
        self.assertTrue(payload["overconstraint_reduced"])
        self.assertTrue(payload["dust_residual_closure_possible"])
        self.assertFalse(payload["full_tensor_closure"])
        self.assertFalse(payload["prediction_ready"])

    def test_equations_are_flow_contractions_only(self) -> None:
        equations = " ".join(row["condition"] + " " + row["scope"] for row in build_payload()["equations"])

        self.assertIn("u_-to+", equations)
        self.assertIn("D_plus", equations)
        self.assertIn("u_+to-", equations)
        self.assertIn("D_minus", equations)
        self.assertIn("dust-flow contraction only", equations)

    def test_risks_block_matter_and_lensing_claims(self) -> None:
        risks = " ".join(build_payload()["risks"])

        self.assertIn("pressure/Pi", risks)
        self.assertIn("lensing rays", risks)
        self.assertIn("E_phi/E_L", risks)

    def test_markdown_reports_conditional_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Dust residual closure possible: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
