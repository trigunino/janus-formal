from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_minimal_phi_dust_test import build_payload, render_markdown


class P0StueckelbergMinimalPhiDustTestTests(unittest.TestCase):
    def test_minimal_phi_dust_test_is_partial_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "minimal-phi-dust-test-partial")
        self.assertFalse(payload["source_derived"])
        self.assertTrue(payload["new_axiom"])
        self.assertFalse(payload["phi_family_unique"])
        self.assertTrue(payload["zero_parameter_branch_available"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_principle_forbids_fit_and_requires_signs(self) -> None:
        principle = " ".join(build_payload()["principle"])

        self.assertIn("mirror symmetry", principle)
        self.assertIn("M15/M30 Newtonian sign laws", principle)
        self.assertIn("no observational parameters", principle)

    def test_zero_parameter_branch_exists_but_does_not_close_map_equations(self) -> None:
        payload = build_payload()
        test = payload["dust_branch_test"]

        self.assertEqual(test["branch"], "zero_parameter_normalized_copy")
        self.assertTrue(test["passes_no_fit"])
        self.assertTrue(test["defines_k_plus_k_minus"])
        self.assertTrue(test["ties_qcross_to_same_l"])
        self.assertFalse(test["closes_e_phi_e_l"])

    def test_markdown_reports_next_required_residual_work(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("transported dust continuity", markdown)
        self.assertIn("R_plus/R_minus", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
