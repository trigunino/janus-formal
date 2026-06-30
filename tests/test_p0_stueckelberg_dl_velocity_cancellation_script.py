from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_dl_velocity_cancellation import (
    build_payload,
    render_markdown,
)


class P0StueckelbergDlVelocityCancellationTests(unittest.TestCase):
    def test_artifact_is_zero_parameter_conditional_and_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dl-velocity-tetrad-cancellation-conditional-open")
        self.assertEqual(payload["branch"], "zero_parameter_stueckelberg_dust")
        self.assertFalse(payload["fit_used"])
        self.assertEqual(payload["free_parameters"], [])
        self.assertEqual(payload["dl_tetrad_terms_cancel"], "conditional")
        self.assertEqual(payload["dl_velocity_terms_cancel"], "conditional")
        self.assertFalse(payload["connection_difference_residual_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_required_cancellation_inputs_are_present(self) -> None:
        payload = build_payload()
        inputs = {row["input"] for row in payload["cancellation_inputs"]}

        self.assertIn("E_L", inputs)
        self.assertIn("Lorentz constraint", inputs)
        self.assertIn("same-L K/Qcross", inputs)
        self.assertIn("transported geodesic dust", inputs)
        self.assertIn("transported dust continuity", inputs)
        self.assertTrue(payload["same_l_k_qcross_required"])
        self.assertTrue(payload["e_l_included"])
        self.assertTrue(payload["lorentz_constraint_included"])
        self.assertTrue(payload["transported_geodesic_included"])
        self.assertTrue(payload["transported_continuity_included"])

    def test_residual_terms_include_dl_velocity_tetrad_and_connection_difference(self) -> None:
        payload = build_payload()
        text = " ".join(row["term"] + " " + row["schematic"] for row in payload["residual_terms"])

        self.assertIn("D_L transported tetrad", text)
        self.assertIn("D_self L", text)
        self.assertIn("D_L transported velocity", text)
        self.assertIn("D_self_nu u_to", text)
        self.assertIn("connection-difference residual", text)
        self.assertIn("C_self-other", text)
        self.assertTrue(payload["connection_difference_residual_included"])

    def test_both_plus_and_minus_k_residuals_are_covered(self) -> None:
        sectors = {row["sector"]: row for row in build_payload()["sectors"]}

        self.assertIn("plus", sectors)
        self.assertIn("minus", sectors)
        self.assertIn("K_plus", sectors["plus"]["k_tensor"])
        self.assertIn("K_minus", sectors["minus"]["k_tensor"])
        self.assertIn("D_plus_nu", sectors["plus"]["residual"])
        self.assertIn("D_minus_nu", sectors["minus"]["residual"])
        self.assertEqual(sectors["plus"]["transport_connection"], "C_plus-minus")
        self.assertEqual(sectors["minus"]["transport_connection"], "C_minus-plus")
        self.assertFalse(sectors["plus"]["closed"])
        self.assertFalse(sectors["minus"]["closed"])

    def test_markdown_reports_open_connection_residual_and_no_fit(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Fit used: False", markdown)
        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Connection-difference residual closed: False", markdown)
        self.assertIn("E_L", markdown)
        self.assertIn("same-L K/Qcross", markdown)


if __name__ == "__main__":
    unittest.main()
