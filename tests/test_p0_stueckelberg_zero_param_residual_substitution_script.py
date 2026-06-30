from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_zero_param_residual_substitution import (
    build_payload,
    render_markdown,
)


class P0StueckelbergZeroParamResidualSubstitutionTests(unittest.TestCase):
    def test_zero_parameter_substitution_is_not_closed_or_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "zero-param-k-substituted-residuals-open")
        self.assertEqual(payload["branch"], "zero_parameter_normalized_copy")
        self.assertFalse(payload["fit_used"])
        self.assertEqual(payload["free_parameters"], [])
        self.assertTrue(payload["k_tensors_listed"])
        self.assertTrue(payload["symbolic_substitution_written"])
        self.assertTrue(payload["obligation_level_only"])
        self.assertFalse(payload["all_remaining_terms_vanish"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["r_minus_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_k_plus_and_k_minus_are_listed_from_source_copy_branch(self) -> None:
        sources = {row["sector"]: row for row in build_payload()["k_sources"]}

        self.assertIn("plus", sources)
        self.assertIn("minus", sources)
        self.assertIn("K_plus", sources["plus"]["k_tensor"])
        self.assertIn("K_minus", sources["minus"]["k_tensor"])
        self.assertIn("rho_minus_to_plus", sources["plus"]["source_copy"])
        self.assertIn("rho_plus_to_minus", sources["minus"]["source_copy"])
        self.assertEqual(sources["plus"]["free_parameters"], [])
        self.assertEqual(sources["minus"]["free_parameters"], [])

    def test_residual_substitutions_cover_both_targets_and_remaining_terms(self) -> None:
        payload = build_payload()
        text = " ".join(
            row["target"] + " " + row["substitution"] + " " + row["obligation_level_expansion"]
            for row in payload["residual_substitutions"]
        )
        remaining = " ".join(payload["remaining_terms"])

        self.assertIn("R_plus", text)
        self.assertIn("R_minus", text)
        self.assertIn("D_phi", text)
        self.assertIn("D_L", text)
        self.assertIn("connection difference", remaining)
        self.assertIn("DlogB", remaining)
        self.assertIn("continuity mismatch", remaining)

    def test_closure_rule_requires_all_remaining_terms_to_vanish(self) -> None:
        payload = build_payload()

        self.assertIn("every remaining term", payload["closure_rule"])
        self.assertTrue(payload["vanish_status"])
        self.assertTrue(all(value is False for value in payload["vanish_status"].values()))
        self.assertFalse(payload["all_remaining_terms_vanish"])

    def test_markdown_reports_no_fit_and_false_prediction_gate(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Fit used: False", markdown)
        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("K_plus", markdown)
        self.assertIn("K_minus", markdown)


if __name__ == "__main__":
    unittest.main()
