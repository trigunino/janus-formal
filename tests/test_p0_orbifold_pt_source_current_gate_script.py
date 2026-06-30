from __future__ import annotations

import unittest

from scripts.build_p0_orbifold_pt_source_current_gate import build_payload, render_markdown


class P0OrbifoldPTSourceCurrentGateTests(unittest.TestCase):
    def test_source_current_gate_is_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "orbifold-pt-source-current-gate-open")
        self.assertEqual(payload["current_equation"], "D_A *F_PT = J_defect + J_matter")
        self.assertTrue(payload["covariant_current_candidates_written"])
        self.assertFalse(payload["defect_current_source_derived"])
        self.assertFalse(payload["matter_current_source_derived"])
        self.assertTrue(payload["observable_fit_current_rejected"])
        self.assertFalse(payload["unique_current_selected"])
        self.assertFalse(payload["a_pt_euler_equation_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_defect_matter_vlasov_and_rejected_fit(self) -> None:
        rows = {row["source"]: row for row in build_payload()["source_rows"]}

        self.assertEqual(
            set(rows),
            {
                "defect_curvature_jump",
                "defect_tension_current",
                "matter_solder_torque",
                "vlasov_phase_space_current",
                "observable_residual_current",
            },
        )
        self.assertTrue(rows["defect_curvature_jump"]["covariant"])
        self.assertTrue(rows["matter_solder_torque"]["pt_compatible"])
        self.assertFalse(rows["observable_residual_current"]["accepted"])
        self.assertIn("forbidden", rows["observable_residual_current"]["blocker"])

    def test_no_current_is_accepted_yet(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["accepted_source_currents"], [])
        self.assertEqual(
            set(payload["admissible_but_unaccepted_sources"]),
            {
                "defect_curvature_jump",
                "defect_tension_current",
                "matter_solder_torque",
                "vlasov_phase_space_current",
            },
        )

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Orbifold/PT Source Current Gate", markdown)
        self.assertIn("Defect current source-derived: False", markdown)
        self.assertIn("Matter current source-derived: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
