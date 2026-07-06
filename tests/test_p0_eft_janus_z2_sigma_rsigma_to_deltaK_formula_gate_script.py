from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_rsigma_to_deltaK_formula_gate import (
    build_payload,
    render_markdown,
)


class RSigmaToDeltaKFormulaGateTests(unittest.TestCase):
    def test_formula_ready_but_values_block_on_active_inputs(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["formula_ready"])
        self.assertFalse(payload["values_ready"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(
            payload["primary_blocker"],
            "R_Sigma_solution_certificate_and_active_embedding_manifest",
        )
        self.assertTrue(payload["bulk_metric_route"]["embedding_second_form_route_preferred"])
        self.assertFalse(payload["bulk_metric_route"]["static_f_pm_values_ready"])

    def test_formula_contains_dynamic_shell_components(self) -> None:
        formulas = build_payload()["formulas"]

        self.assertIn("sqrt(Rdot^2 + f_pm(R))", formulas["K_s_pm"])
        self.assertIn("0.5 f_pm'(R)", formulas["K_tau_pm"])
        self.assertIn("eps_Z2", formulas["DeltaK_s"])

    def test_markdown_reports_formula_ready(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("R_Sigma to DeltaK", markdown)
        self.assertIn("Formula ready: `True`", markdown)


if __name__ == "__main__":
    unittest.main()
