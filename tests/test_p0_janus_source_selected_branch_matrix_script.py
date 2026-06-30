from __future__ import annotations

import unittest

from scripts.build_p0_janus_source_selected_branch_matrix import build_payload, render_markdown


class P0JanusSourceSelectedBranchMatrixTests(unittest.TestCase):
    def test_qdet_is_conditionally_selected_without_double_counting(self) -> None:
        payload = build_payload()
        branches = {row["branch"]: row for row in payload["branches"]}

        self.assertTrue(payload["qdet_branch_conditionally_selected"])
        self.assertIn("q_det=1", branches["qdet_density_convention"]["selection"])
        self.assertIn("weighted the active source", branches["qdet_density_convention"]["selection"])
        self.assertIn("twice", branches["qdet_density_convention"]["forbidden"])

    def test_background_and_boundary_remain_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["background_zero_mode_globally_selected"])
        self.assertFalse(payload["boundary_gauge_physically_selected"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_same_l_selection_is_only_flrw_identity(self) -> None:
        payload = build_payload()
        branches = {row["branch"]: row for row in payload["branches"]}

        self.assertTrue(payload["flrw_comoving_same_l_identity_selected"])
        self.assertTrue(payload["weakfield_scalar_lorentz_projection_selected_identity"])
        self.assertTrue(payload["weakfield_shift_boost_projection_derived"])
        self.assertTrue(payload["janus_0i_shift_source_operator_closed"])
        self.assertFalse(payload["pressure_pi0i_transport_closed"])
        self.assertFalse(payload["same_l_global_perturbed_branch_selected"])
        self.assertIn("L=I", branches["same_l_for_k_qcross"]["selection"])
        self.assertIn("eta-skew", branches["same_l_for_k_qcross"]["selection"])
        self.assertIn("F_i0=Delta_B_i/2", branches["same_l_for_k_qcross"]["selection"])
        self.assertIn("G0i shift operator", branches["same_l_for_k_qcross"]["selection"])
        self.assertIn("one L for Q_cross and another", branches["same_l_for_k_qcross"]["forbidden"])

    def test_no_fit_or_scalar_absorption(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-selected-branch-matrix-open")
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_scalar_absorption"])

    def test_markdown_reports_partial_selection(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Q_det branch conditionally selected: True", markdown)
        self.assertIn("Same-L global perturbed branch selected: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
