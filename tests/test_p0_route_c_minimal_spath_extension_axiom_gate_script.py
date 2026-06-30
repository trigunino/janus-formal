from __future__ import annotations

import unittest

from scripts.build_p0_route_c_minimal_spath_extension_axiom_gate import (
    build_payload,
    render_markdown,
)


class P0RouteCMinimalSpathExtensionAxiomGateTests(unittest.TestCase):
    def test_spath_extension_is_explicit_not_source_derived_or_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "minimal-spath-extension-axiom-proposed-not-predictive")
        self.assertTrue(payload["extension_is_explicit"])
        self.assertFalse(payload["source_derived_from_published_janus"])
        self.assertTrue(payload["new_axiom_declared"])
        self.assertFalse(payload["new_axiom_adopted_for_prediction"])
        self.assertFalse(payload["can_be_used_for_prediction_now"])
        self.assertFalse(payload["prediction_ready"])

    def test_action_terms_cover_path_transport_mirror_and_boundary(self) -> None:
        terms = {row["term"] for row in build_payload()["action_terms"]}

        self.assertEqual(
            terms,
            {
                "path_selector",
                "lorentz_transport",
                "pt_mirror_inverse",
                "boundary_law",
            },
        )
        self.assertTrue(all(not row["accepted"] for row in build_payload()["action_terms"]))

    def test_acceptance_gates_keep_only_traceability_and_no_fit_passed(self) -> None:
        payload = build_payload()
        gates = {row["gate"]: row for row in payload["acceptance_rows"]}

        self.assertTrue(gates["declared_extension"]["passed"])
        self.assertTrue(gates["no_fit_no_absorption"]["passed"])
        self.assertFalse(gates["same_l_stack"]["passed"])
        self.assertFalse(gates["euler_lagrange_equations"]["passed"])
        self.assertFalse(gates["bianchi_noether_closure"]["passed"])
        self.assertFalse(gates["stability_screen"]["passed"])
        self.assertTrue(payload["forbids_observational_fit"])
        self.assertTrue(payload["forbids_qdet_qcross_absorption"])

    def test_markdown_reports_non_predictive_extension(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Minimal S_path Extension Axiom", markdown)
        self.assertIn("Source-derived from published Janus: False", markdown)
        self.assertIn("New axiom adopted for prediction: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
