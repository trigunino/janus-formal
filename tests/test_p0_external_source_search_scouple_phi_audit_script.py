from __future__ import annotations

import unittest

from scripts.build_p0_external_source_search_scouple_phi_audit import (
    build_payload,
    render_markdown,
)


class P0ExternalSourceSearchScouplePhiAuditTests(unittest.TestCase):
    def test_audit_is_external_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "external-source-search-scouple-phi-open")
        self.assertTrue(payload["external_search_performed"])
        self.assertTrue(payload["coupled_field_equation_sources_found"])
        self.assertFalse(payload["scouple_phi_source_found"])
        self.assertFalse(payload["explicit_variational_transport_law_found"])
        self.assertFalse(payload["omega_u_zero_source_law_found"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["prediction_claim"])

    def test_sources_include_urls_and_relevant_coupled_field_anchors(self) -> None:
        payload = build_payload()
        rows = " ".join(
            row["title"] + " " + row["url"] + " " + row["relevant_content"]
            for row in payload["sources"]
        )

        self.assertGreaterEqual(payload["source_count"], 5)
        self.assertIn("https://ui.adsabs.harvard.edu/abs/2015Ap%26SS.357...67P/abstract", rows)
        self.assertIn("https://www.jp-petit.org/papers/cosmo/2014-ModPhysLettA.pdf", rows)
        self.assertIn("coupled field equations", rows)
        self.assertIn("Lagrangian derivation", rows)

    def test_exact_search_terms_cover_required_notation(self) -> None:
        terms = " ".join(build_payload()["exact_search_terms"])

        self.assertIn("S_couple", terms)
        self.assertIn("Phi_bar", terms)
        self.assertIn("Omega_u", terms)
        self.assertIn("D_u L", terms)

    def test_markdown_renders_citations_and_explicit_no_closure(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("| id | title | URL | relevant content | transport law status |", markdown)
        self.assertIn("Explicit variational transport law found: False", markdown)
        self.assertIn("Omega_u u=0 source law found: False", markdown)
        self.assertIn("Prediction claim: False", markdown)
        self.assertIn("https://hal.science/hal-04583560v1/document", markdown)
        self.assertIn("did not find an explicit variational transport law", markdown)


if __name__ == "__main__":
    unittest.main()
