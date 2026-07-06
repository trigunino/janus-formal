from __future__ import annotations

import unittest

from scripts.build_p0_eft_janus_z2_sigma_alpha_radial_coefficients_bibliography_gate import (
    build_payload,
    render_markdown,
)


class AlphaRadialCoefficientsBibliographyGateTests(unittest.TestCase):
    def test_bibliography_selects_route_but_does_not_close_coefficients(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["bibliography_checked"])
        self.assertTrue(payload["bibliography_selects_route"])
        self.assertFalse(payload["bibliography_closes_alpha_h_alpha_K"])
        self.assertEqual(
            payload["route"]["active_route"],
            "geometric_surface_stress_plus_bending_moment",
        )

    def test_sources_include_membrane_junction_and_bending_moment_references(self) -> None:
        keys = {source["key"] for source in build_payload()["sources"]}

        self.assertIn("Armas_Tarrio_2017_surface_actions_DCFT", keys)
        self.assertIn("PhysRevE_101_062803_membrane_EFT", keys)
        self.assertIn("Capovilla_Guven_1995", keys)
        self.assertIn("Carter_2001_brane_dynamics", keys)
        self.assertIn("Mars_Senovilla_2002", keys)
        self.assertIn("blackfold_elastic_expansion", keys)

    def test_markdown_reports_radial_pullback(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Radial Pullback", markdown)
        self.assertIn("alpha_h_radial", markdown)
        self.assertIn("alpha_K_radial", markdown)


if __name__ == "__main__":
    unittest.main()
