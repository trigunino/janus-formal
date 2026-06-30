from __future__ import annotations

import unittest

from scripts.build_p0_m30_zero_divergence_pde_derivation import build_payload


class P0M30ZeroDivergencePdeDerivationTests(unittest.TestCase):
    def test_source_principle_yields_pde_but_not_prediction(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["zero_divergence_principle_source_anchored"])
        self.assertTrue(payload["pde_system_written"])
        self.assertTrue(payload["b4vol_inside_pde"])
        self.assertTrue(payload["f_alpha_constrained_not_solved"])
        self.assertFalse(payload["unique_solution_found"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_pde_system_has_plus_and_minus_rows(self) -> None:
        rows = {row["sector"]: row for row in build_payload()["pde_system"]}

        self.assertIn("D_plus_nu(B_4vol_plus_from_minus K_plus", rows["plus"]["equation"])
        self.assertIn("D_minus_nu(B_4vol_minus_from_plus K_minus", rows["minus"]["equation"])
        self.assertIn("D_plus_nu T_plus", rows["plus"]["equation"])
        self.assertIn("D_minus_nu T_minus", rows["minus"]["equation"])

    def test_f_alpha_is_constrained_not_solved(self) -> None:
        text = " ".join(build_payload()["link_to_f_alpha"])

        self.assertIn("F_alpha=(D_alpha L)L^{-1}", text)
        self.assertIn("divergence-visible contractions", text)
        self.assertIn("F_alpha^T eta + eta F_alpha=0", text)
        self.assertIn("uniqueness", text)

    def test_solved_now_and_open_items_are_separated(self) -> None:
        payload = build_payload()
        solved = " ".join(payload["solved_now"])
        open_items = " ".join(payload["still_open"])

        self.assertIn("M30 zero-divergence PDE target", solved)
        self.assertIn("B_4vol product-rule terms", solved)
        self.assertIn("closed-form K_plus/K_minus", open_items)
        self.assertIn("unique F_alpha", open_items)
        self.assertIn("Q_cross normalization", open_items)


if __name__ == "__main__":
    unittest.main()
