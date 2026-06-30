from __future__ import annotations

import unittest

from scripts.build_p0_external_janus_omega_source_search_gate import build_payload, render_markdown


class P0ExternalJanusOmegaSourceSearchGateTests(unittest.TestCase):
    def test_gate_is_artifact_only_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "external-janus-omega-source-search-gate-open")
        self.assertEqual(payload["target_count"], 4)
        self.assertIn("no browsing performed", payload["scope"])
        self.assertFalse(payload["external_search_performed"])
        self.assertTrue(payload["external_janus_omega_source_search_results_available"])
        self.assertFalse(payload["source_law_found"])
        self.assertFalse(payload["unsourced_closure_allowed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["prediction_claim"])

    def test_evidence_targets_cover_required_external_search_items(self) -> None:
        rows = " ".join(
            row["target"] + " " + row["search_for"] + " " + row["accept_if"] + " " + row["reject_if"]
            for row in build_payload()["evidence_targets"]
        )

        self.assertIn("D_u L", rows)
        self.assertIn("FW/comoving", rows)
        self.assertIn("Fermi-Walker", rows)
        self.assertIn("source congruence/cross-force", rows)
        self.assertIn("S_couple/Phi", rows)
        self.assertIn("Omega_u u=0", rows)

    def test_acceptance_and_rejection_rules_block_unsourced_closure(self) -> None:
        payload = build_payload()
        rules = " ".join(payload["rejection_rules"])

        self.assertTrue(payload["acceptance_requires_external_source"])
        self.assertTrue(payload["acceptance_requires_equation_trace"])
        self.assertTrue(payload["acceptance_requires_omega_u_zero_transport"])
        self.assertTrue(payload["acceptance_requires_no_gauge_fit"])
        self.assertIn("unsourced convention", rules)
        self.assertIn("post-residual gauge fit", rules)
        self.assertIn("no prediction claim", rules)
        self.assertIn("D_u L transport", rules)

    def test_markdown_renders_targets_and_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("| target | search for | accept if | reject if |", markdown)
        self.assertIn("D_u L transport law", markdown)
        self.assertIn("Unsourced closure allowed: False", markdown)
        self.assertIn("Prediction claim: False", markdown)
        self.assertIn("no browsing performed", markdown)


if __name__ == "__main__":
    unittest.main()
