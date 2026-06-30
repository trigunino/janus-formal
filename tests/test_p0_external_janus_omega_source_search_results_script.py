from __future__ import annotations

import unittest

from scripts.build_p0_external_janus_omega_source_search_results import build_payload


class P0ExternalJanusOmegaSourceSearchResultsTests(unittest.TestCase):
    def test_search_results_are_non_predictive_and_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "external-search-performed-no-omega-source-found")
        self.assertTrue(payload["external_search_performed"])
        self.assertTrue(payload["external_source_search_omega_transport_audit_available"])
        self.assertTrue(payload["external_source_search_scouple_phi_audit_available"])
        self.assertTrue(payload["b4vol_bianchi_source_found"])
        self.assertTrue(payload["k_tensor_source_found"])
        self.assertFalse(payload["du_l_transport_source_found"])
        self.assertFalse(payload["omega_u_zero_source_found"])
        self.assertFalse(payload["prediction_ready"])

    def test_sources_include_urls_and_missing_omega_law(self) -> None:
        text = " ".join(
            row["url"] + row["found"] + row["missing_for_omega"] for row in build_payload()["sources"]
        )

        self.assertIn("jp-petit.org/papers/cosmo", text)
        self.assertIn("januscosmologicalmodel.com/map", text)
        self.assertIn("coupled field equations", text)
        self.assertIn("D_u L", text)
        self.assertIn("Omega_u u=0", text)

    def test_search_terms_cover_transport_fw_scouple_and_bianchi(self) -> None:
        terms = " ".join(build_payload()["search_terms"])

        self.assertIn("D_u L", terms)
        self.assertIn("Fermi-Walker", terms)
        self.assertIn("S_couple Phi", terms)
        self.assertIn("Bianchi K tensor", terms)


if __name__ == "__main__":
    unittest.main()
