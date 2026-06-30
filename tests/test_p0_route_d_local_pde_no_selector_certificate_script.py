from __future__ import annotations

import unittest

from scripts.build_p0_route_d_local_pde_no_selector_certificate import (
    build_payload,
    render_markdown,
)


class P0RouteDLocalPDENoSelectorCertificateTests(unittest.TestCase):
    def test_certificate_closes_bounded_claim_only(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "local-source-free-boundary-free-pde-no-selector-certified")
        self.assertTrue(payload["numeric_probes_are_witnesses_only"])
        self.assertFalse(payload["local_source_free_boundary_free_pde_selects_l"])
        self.assertTrue(payload["selection_requires_source_or_boundary_axiom"])
        self.assertTrue(payload["bounded_claim_closed"])
        self.assertFalse(payload["full_no_go_proved"])
        self.assertEqual(payload["open_escape"], "source-derived STF curvature operator")
        self.assertFalse(payload["prediction_ready"])

    def test_lemmas_cover_kernel_boundary_structural_and_omega_law(self) -> None:
        lemmas = {row["lemma"] for row in build_payload()["lemmas"]}

        self.assertEqual(
            lemmas,
            {
                "homogeneous_local_pde",
                "invertible_operator_not_enough",
                "structural_boundaries_underselect",
                "strong_boundary_selectors",
                "omega_law_missing",
            },
        )

    def test_markdown_reports_certificate(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("No-Selector Certificate", markdown)
        self.assertIn("Bounded claim closed: True", markdown)
        self.assertIn("Full no-go proved: False", markdown)


if __name__ == "__main__":
    unittest.main()
