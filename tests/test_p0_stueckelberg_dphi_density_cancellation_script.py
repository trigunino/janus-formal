from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_dphi_density_cancellation import (
    build_payload,
    render_markdown,
)


class P0StueckelbergDphiDensityCancellationTests(unittest.TestCase):
    def test_artifact_is_conditional_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dphi-density-cancellation-conditional-open")
        self.assertEqual(payload["branch"], "zero_parameter_normalized_copy")
        self.assertFalse(payload["fit_used"])
        self.assertEqual(payload["free_parameters"], [])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_density_maps_cover_pullback_pushforward_and_continuity(self) -> None:
        text = " ".join(
            row["direction"] + " " + row["map"] + " " + row["continuity"]
            for row in build_payload()["density_maps"]
        )

        self.assertIn("minus_to_plus", text)
        self.assertIn("plus_to_minus", text)
        self.assertIn("rho_minus_to_plus", text)
        self.assertIn("rho_plus_to_minus", text)
        self.assertIn("transported by phi", text)
        self.assertIn("transported by phi^{-1}", text)

    def test_required_identities_are_listed_and_not_proven_here(self) -> None:
        identities = {row["name"]: row for row in build_payload()["required_identities"]}

        self.assertIn("jacobian_volume_identity", identities)
        self.assertIn("lie_derivative_density_relation", identities)
        self.assertIn("determinant_B_consistency", identities)
        self.assertIn("sqrt|g_plus|", identities["jacobian_volume_identity"]["equation"])
        self.assertIn("L_u", identities["lie_derivative_density_relation"]["equation"])
        self.assertIn("D log B", identities["determinant_B_consistency"]["equation"])
        self.assertTrue(all(row["proven_here"] is False for row in identities.values()))

    def test_cancellation_is_conditional_without_fit(self) -> None:
        payload = build_payload()
        decision = payload["closure_decision"]

        self.assertEqual(decision["dphi_density_terms_cancel"], "conditional")
        self.assertFalse(decision["closure"])
        self.assertTrue(decision["conditional_closure_possible"])
        self.assertIn("same phi", decision["reason"])
        self.assertTrue(all(row["fit_used"] is False for row in payload["cancellation_tests"]))

    def test_markdown_reports_false_closure_and_required_terms(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Fit used: False", markdown)
        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Closure: False", markdown)
        self.assertIn("jacobian_volume_identity", markdown)
        self.assertIn("lie_derivative_density_relation", markdown)
        self.assertIn("determinant_B_consistency", markdown)


if __name__ == "__main__":
    unittest.main()
