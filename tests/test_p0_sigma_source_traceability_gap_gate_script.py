from __future__ import annotations

import unittest

from scripts.build_p0_sigma_source_traceability_gap_gate import (
    build_payload,
    render_markdown,
)


class P0SigmaSourceTraceabilityGapGateTests(unittest.TestCase):
    def test_gap_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "sigma-source-traceability-gap-open")
        self.assertTrue(payload["latest_web_search_performed"])
        self.assertFalse(payload["published_sigma_dh_source_found"])
        self.assertFalse(payload["published_phi_sigma_source_found"])
        self.assertFalse(payload["published_nonmetricity_source_found"])
        self.assertFalse(payload["closure_allowed_from_source"])
        self.assertFalse(payload["prediction_ready"])

    def test_sources_checked_include_current_janus_anchors(self) -> None:
        text = " ".join(row["source"] + " " + row["url"] for row in build_payload()["sources_checked"])

        self.assertIn("Janus official map", text)
        self.assertIn("hal-04583560", text)
        self.assertIn("2026-Expansion-exact-solution", text)
        self.assertIn("QUESTIONABLE-BLACK-HOLES", text)

    def test_allowed_next_keeps_original_derivation_or_axiom_explicit(self) -> None:
        text = " ".join(build_payload()["allowed_next"])

        self.assertIn("derive Sigma/DH as original work", text)
        self.assertIn("clearly labeled new no-fit axiom", text)
        self.assertIn("prove no local low-derivative", text)

    def test_guardrails_prevent_overclaiming_search_results(self) -> None:
        text = " ".join(build_payload()["guardrails"])

        self.assertIn("not a proof of nonexistence", text)
        self.assertIn("do not cite Bianchi/K tensors", text)
        self.assertIn("PDF equation verification", text)

    def test_markdown_reports_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Sigma Source Traceability Gap", markdown)
        self.assertIn("Published Sigma/DH source found: False", markdown)
        self.assertIn("Sources Checked", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
