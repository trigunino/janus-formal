from __future__ import annotations

import unittest

from scripts.build_p0_janus_equations_to_l_omega_law_attempt import (
    build_payload,
    render_markdown,
)


class P0JanusEquationsToLOmegaLawAttemptTests(unittest.TestCase):
    def test_attempt_is_open_and_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-equations-to-l-omega-law-attempt-open")
        self.assertFalse(payload["du_l_selected"])
        self.assertFalse(payload["omega_u_u_zero_selected"])
        self.assertFalse(payload["source_equations_fully_inserted"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_encodes_janus_equation_ingredients(self) -> None:
        text = " ".join(
            row["ingredient"] + row["source"] + row["encoded_as"]
            for row in build_payload()["janus_ingredients"]
        )

        self.assertIn("coupled_metrics", text)
        self.assertIn("G_plus=chi", text)
        self.assertIn("G_minus=-chi", text)
        self.assertIn("B_plus=sqrt(-g_minus/-g_plus)", text)
        self.assertIn("Bianchi", text)
        self.assertIn("K_plus", text)

    def test_constraints_do_not_select_dynamic_law(self) -> None:
        payload = build_payload()
        laws = {row["law"]: row for row in payload["candidate_laws"]}
        reduction = " ".join(
            row["result"] + row["imposes_on_l_omega"]
            for row in payload["constraint_reduction"]
        )

        self.assertFalse(laws["dynamic_du_l"]["selected_by_janus_equations"])
        self.assertFalse(laws["omega_u_u_zero"]["selected_by_janus_equations"])
        self.assertIn("does not fix", laws["dynamic_du_l"]["constraint"])
        self.assertIn("not a source-derived law", laws["omega_u_u_zero"]["constraint"])
        self.assertIn("D K contains", reduction)
        self.assertIn("residual can test a proposed Omega", reduction)

    def test_same_l_for_k_qcross_and_no_shortcuts(self) -> None:
        payload = build_payload()
        blockers = " ".join(payload["blockers"])
        reduction = " ".join(row["result"] for row in payload["constraint_reduction"])

        self.assertTrue(payload["same_l_for_k_qcross_required"])
        self.assertFalse(payload["same_l_for_k_qcross_derived"])
        self.assertFalse(payload["fitting_allowed"])
        self.assertFalse(payload["scalar_absorption_allowed"])
        self.assertIn("same transported tetrads", reduction)
        self.assertIn("No fit", blockers)
        self.assertIn("scalar absorption", blockers)

    def test_markdown_renders_selection_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("D_u L selected: False", markdown)
        self.assertIn("Omega_u u=0 selected: False", markdown)
        self.assertIn("Same L for K/Q_cross required: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
