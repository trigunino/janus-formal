from __future__ import annotations

import unittest

from scripts.build_p0_bianchi_minimal_mirror_inverse_attempt import (
    build_payload,
    render_markdown,
)


class P0BianchiMinimalMirrorInverseAttemptTests(unittest.TestCase):
    def test_attempt_starts_from_joint_branch_and_gate_but_remains_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "mirror-inverse-consistency-attempt-open")
        self.assertIn("p0_bianchi_minimal_joint_dl_dlogb_solution", payload["starts_from"])
        self.assertIn("p0_bianchi_minimal_integrability_mirror_gate", payload["starts_from"])
        self.assertTrue(payload["inverse_map_written"])
        self.assertTrue(payload["omega_inverse_transport_written"])
        self.assertTrue(payload["b4vol_reciprocity_written"])
        self.assertFalse(payload["mirror_inverse_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_inverse_map_equations_are_explicit(self) -> None:
        equations = " ".join(row["formula"] + row["role"] for row in build_payload()["inverse_map_equations"])

        self.assertIn("L_pm=L_mp^{-1}", equations)
        self.assertIn("Omega_alpha_mp=-L_pm^{-1} Omega_alpha_pm L_pm", equations)
        self.assertIn("sector-connection conversion", equations)
        self.assertIn("B_4vol_pm B_4vol_mp=1", equations)
        self.assertIn("not independent fit knobs", equations)

    def test_local_flow_branch_implies_two_open_residual_rows(self) -> None:
        payload = build_payload()
        rows = {row["row"]: row for row in payload["residual_rows"]}
        implications = " ".join(
            row["longitudinal_condition"] + row["transverse_condition"]
            for row in payload["local_flow_implications"]
        )

        self.assertTrue(payload["local_flow_branch_implications_written"])
        self.assertTrue(payload["both_residual_rows_required"])
        self.assertFalse(payload["both_residual_rows_closed"])
        self.assertEqual(set(rows), {"plus_receives_minus", "minus_receives_plus"})
        self.assertFalse(rows["plus_receives_minus"]["closed"])
        self.assertFalse(rows["minus_receives_plus"]["closed"])
        self.assertIn("u_pm.D_plus log B_4vol_pm", implications)
        self.assertIn("h_pm Omega_u_pm u_pm", implications)
        self.assertIn("u_mp.D_minus log B_4vol_mp", implications)
        self.assertIn("h_mp Omega_u_mp u_mp", implications)

    def test_same_l_for_qcross_required_and_shortcuts_forbidden(self) -> None:
        payload = build_payload()
        requirements = {row["requirement"]: row for row in payload["consistency_requirements"]}
        details = " ".join(row["detail"] for row in payload["consistency_requirements"])

        self.assertTrue(payload["same_l_for_qcross_required"])
        self.assertFalse(payload["fitting_allowed"])
        self.assertFalse(payload["scalar_absorption_allowed"])
        self.assertFalse(requirements["same_l_for_qcross"]["closed"])
        self.assertTrue(requirements["no_fit"]["closed"])
        self.assertTrue(requirements["no_scalar_absorption"]["closed"])
        self.assertIn("same inverse-paired L_pm/L_mp", details)
        self.assertIn("do not tune", details)
        self.assertIn("do not absorb residual rows", details)

    def test_markdown_renders_open_mirror_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Both residual rows closed: False", markdown)
        self.assertIn("Mirror inverse closed: False", markdown)
        self.assertIn("Same L for Q_cross required: True", markdown)
        self.assertIn("Fitting allowed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
