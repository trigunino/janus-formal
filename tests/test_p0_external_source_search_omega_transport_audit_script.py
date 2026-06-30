from __future__ import annotations

import unittest

from scripts.build_p0_external_source_search_omega_transport_audit import (
    build_payload,
    render_markdown,
)


class P0ExternalSourceSearchOmegaTransportAuditTests(unittest.TestCase):
    def test_audit_records_search_but_keeps_prediction_false(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "external-source-search-omega-transport-audit-open")
        self.assertTrue(payload["external_search_performed"])
        self.assertFalse(payload["explicit_equation_found"])
        self.assertFalse(payload["source_law_found"])
        self.assertFalse(payload["omega_u_zero_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["prediction_claim"])

    def test_search_targets_cover_requested_terms(self) -> None:
        text = " ".join(payload_text(build_payload()))

        self.assertIn("D_u L", text)
        self.assertIn("Fermi-Walker", text)
        self.assertIn("comoving tetrad", text)
        self.assertIn("L transport", text)
        self.assertIn("geodesic", text)
        self.assertIn("Omega_u u=0", text)

    def test_sources_have_urls_and_no_explicit_transport_equation(self) -> None:
        payload = build_payload()

        self.assertGreaterEqual(len(payload["sources"]), 4)
        self.assertTrue(all(source["url"].startswith("https://") for source in payload["sources"]))
        self.assertTrue(all(not source["explicit_transport_equation_found"] for source in payload["sources"]))

    def test_markdown_contains_citations_and_non_closure_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("https://januscosmologicalmodel.com/negativemass", markdown)
        self.assertIn("https://arxiv.org/html/2412.04644v3", markdown)
        self.assertIn("Explicit equation found: False", markdown)
        self.assertIn("Prediction claim: False", markdown)
        self.assertIn("Prediction remains false", markdown)


def payload_text(payload: dict) -> list[str]:
    parts: list[str] = [payload["description"], payload["scope"], payload["verdict"]]
    parts.extend(payload["search_queries"])
    for source in payload["sources"]:
        parts.extend([source["title"], source["url"], source["relevant_evidence"]])
    for row in payload["audit_rows"]:
        parts.extend([row["target"], row["result"], row["notes"]])
    return parts


if __name__ == "__main__":
    unittest.main()
