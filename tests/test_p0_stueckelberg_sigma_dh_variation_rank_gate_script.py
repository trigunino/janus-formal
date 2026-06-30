from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_sigma_dh_variation_rank_gate import (
    build_payload,
    render_markdown,
)


class P0StueckelbergSigmaDHVariationRankGateTests(unittest.TestCase):
    def test_current_lorentz_variation_does_not_select_sigma(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "stueckelberg-lorentz-variation-does-not-select-sigma-dh",
        )
        self.assertFalse(payload["stueckelberg_selects_sigma_dh"])
        self.assertTrue(payload["gl_extension_required_for_sigma"])
        self.assertTrue(payload["overconstraint_risk_increases_if_gl_added"])
        self.assertTrue(payload["ghost_gate_required_if_gl_added"])
        self.assertFalse(payload["prediction_ready"])

    def test_rank_count_separates_lorentz_and_symmetric_channels(self) -> None:
        rank = build_payload()["rank_count"]

        self.assertEqual(rank["lorentz_tangent_antisymmetric"], 6)
        self.assertEqual(rank["eta_symmetric_strain_sigma"], 10)
        self.assertEqual(rank["raw_gl_lgeom"], 16)
        self.assertEqual(rank["sigma_rank_hit_by_lorentz_variation"], 0)

    def test_linearized_lorentz_variation_leaves_h_fixed(self) -> None:
        identity = build_payload()["linearized_variation_identity"]

        self.assertIn("A^dagger_eta=-A", identity)
        self.assertIn("delta H", identity)
        self.assertIn("= 0", identity)

    def test_routes_left_require_gl_h_or_nonmetricity_extension(self) -> None:
        text = " ".join(build_payload()["routes_left"])

        self.assertIn("raw L_geom", text)
        self.assertIn("H=eta^{-1}L_geom^T eta L_geom", text)
        self.assertIn("relative nonmetricity", text)

    def test_guardrails_block_false_sigma_claim(self) -> None:
        text = " ".join(build_payload()["guardrails"])

        self.assertIn("do not reinterpret Lorentz E_L", text)
        self.assertIn("ghost/stability gate", text)
        self.assertIn("dust Cuu bridge", text)
        self.assertIn("determinant/B4vol trace", text)

    def test_markdown_reports_remaining_lock(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Stueckelberg Sigma/DH", markdown)
        self.assertIn("sigma_rank_hit_by_lorentz_variation", markdown)
        self.assertIn("GL extension required for Sigma: True", markdown)
        self.assertIn("Remaining lock", markdown)


if __name__ == "__main__":
    unittest.main()
