from __future__ import annotations

import unittest

from scripts.build_p0_minimal_axiom_transport_solution import build_payload


class P0MinimalAxiomTransportSolutionTests(unittest.TestCase):
    def test_branch_closes_only_conditionally(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "conditional-solution-branch")
        self.assertTrue(payload["axiom_branch_written"])
        self.assertTrue(payload["conditional_r_plus_closed"])
        self.assertTrue(payload["conditional_r_minus_closed"])
        self.assertFalse(payload["source_derived"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_axioms_include_densitized_source_lorentz_l_and_mirror(self) -> None:
        text = " ".join(row["statement"] for row in build_payload()["axioms"])

        self.assertIn("S_plus", text)
        self.assertIn("B_4vol_plus_from_minus", text)
        self.assertIn("F_alpha^T eta + eta F_alpha=0", text)
        self.assertIn("L_plus_to_minus=L_minus_to_plus^{-1}", text)
        self.assertIn("Q_cross", text)

    def test_closure_reduction_states_both_residuals(self) -> None:
        reduction = " ".join(build_payload()["closure_reduction"])

        self.assertIn("R_plus", reduction)
        self.assertIn("D_plus_nu S_plus", reduction)
        self.assertIn("R_minus", reduction)
        self.assertIn("D_minus_nu S_minus", reduction)

    def test_unsolved_items_keep_source_and_matter_extension_open(self) -> None:
        unsolved = " ".join(build_payload()["not_yet_solved"])

        self.assertIn("derive A2-A4", unsolved)
        self.assertIn("explicit F_alpha", unsolved)
        self.assertIn("pressure", unsolved)
        self.assertIn("Pi", unsolved)
        self.assertIn("Q_cross normalization", unsolved)

    def test_rejection_rules_prevent_scalar_patches(self) -> None:
        rules = " ".join(build_payload()["rejection_rules"])

        self.assertIn("Q_det again", rules)
        self.assertIn("V3_dust", rules)
        self.assertIn("F_alpha=0", rules)
        self.assertIn("do not claim source proof", rules)


if __name__ == "__main__":
    unittest.main()
