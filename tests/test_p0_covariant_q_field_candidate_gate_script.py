from __future__ import annotations

import unittest

from scripts.build_p0_covariant_q_field_candidate_gate import build_payload, render_markdown


class P0CovariantQFieldCandidateGateTests(unittest.TestCase):
    def test_selects_relative_strain_tensor_conditionally(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "q-field-candidate-selected-conditionally")
        self.assertEqual(payload["selected_candidate"], "relative_strain_tensor_Q")
        self.assertFalse(payload["source_fixed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertEqual(
            payload["selected_candidate_regular_gate"],
            "p0_relative_strain_q_regular_branch_gate",
        )
        self.assertEqual(
            payload["selected_candidate_derivative_gate"],
            "p0_relative_strain_q_derivative_omega_gate",
        )

    def test_odd_transport_is_mirror_consistent(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["symbolic_odd_transport"], "q**3*r3 + q*r1")
        self.assertEqual(payload["mirror_odd_residual"], "0")

    def test_rejects_determinant_as_sole_q_and_raw_lgeom(self) -> None:
        rows = {row["name"]: row for row in build_payload()["candidate_rows"]}

        self.assertIn("underselection", rows["log_b4vol_or_logdet"]["verdict"])
        self.assertFalse(rows["log_b4vol_or_logdet"]["keeps_anisotropic_strain"])
        self.assertFalse(rows["raw_L_geom"]["covariant"])
        self.assertIn("reject", rows["raw_L_geom"]["verdict"])

    def test_selected_q_keeps_anisotropic_same_l_data(self) -> None:
        rows = {row["name"]: row for row in build_payload()["candidate_rows"]}
        selected = rows["relative_strain_tensor_Q"]

        self.assertTrue(selected["covariant"])
        self.assertTrue(selected["mirror_odd"])
        self.assertTrue(selected["keeps_anisotropic_strain"])
        self.assertEqual(selected["selects_l"], "candidate")

    def test_markdown_reports_regular_requirements(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Covariant q/Q Field", markdown)
        self.assertIn("Q=1/2 log(H)", markdown)
        self.assertIn("p0_relative_strain_q_regular_branch_gate", markdown)
        self.assertIn("p0_relative_strain_q_derivative_omega_gate", markdown)
        self.assertIn("FrechetLog_H[D_alpha H]", markdown)
        self.assertIn("same phi/L", markdown)
        self.assertIn("Remaining lock", markdown)


if __name__ == "__main__":
    unittest.main()
