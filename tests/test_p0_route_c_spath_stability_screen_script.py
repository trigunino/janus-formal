from __future__ import annotations

import unittest

from scripts.build_p0_route_c_spath_stability_screen import build_payload, render_markdown


class P0RouteCSPathStabilityScreenTests(unittest.TestCase):
    def test_stability_screen_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "spath-stability-screen-open")
        self.assertTrue(payload["stability_screen_written"])
        self.assertTrue(payload["path_conditions_written"])
        self.assertTrue(payload["lorentz_naive_invariant_indefinite"])
        self.assertTrue(payload["positive_auxiliary_metric_available"])
        self.assertFalse(payload["positive_auxiliary_metric_source_derived"])
        self.assertFalse(payload["boundary_conditions_fixed"])
        self.assertFalse(payload["caustic_multibranch_control_closed"])
        self.assertFalse(payload["ghost_free_proved"])
        self.assertFalse(payload["tachyon_free_proved"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_stability_obligations(self) -> None:
        rows = {row["sector"]: row for row in build_payload()["stability_rows"]}

        self.assertEqual(
            set(rows),
            {
                "path_mode",
                "lorentz_algebra_naive_invariant",
                "lorentz_algebra_positive_auxiliary",
                "boundary_modes",
                "caustic_multibranch",
            },
        )
        self.assertTrue(all(not row["passed"] for row in rows.values()))

    def test_symbolic_forms_expose_required_signs(self) -> None:
        payload = build_payload()

        self.assertIn("C_0", payload["path_quadratic_form"])
        self.assertIn("V_2", payload["path_quadratic_form"])
        self.assertIn("-b_x**2", payload["lorentz_killing_quadratic"])
        self.assertIn("r_x**2", payload["lorentz_killing_quadratic"])
        self.assertIn("b_x**2", payload["positive_algebra_quadratic"])
        self.assertIn("r_z**2", payload["positive_algebra_quadratic"])

    def test_instability_flags_are_explicit(self) -> None:
        flags = {row["flag"]: row["condition"] for row in build_payload()["instability_flags"]}

        self.assertEqual(flags["path_wrong_sign_kinetic"], "C_0 <= 0")
        self.assertEqual(flags["path_tachyon"], "V_2 < 0")
        self.assertEqual(flags["lorentz_indefinite_norm"], "using -1/2 Tr(Xi^2) as positive energy")
        self.assertEqual(flags["boundary_negative_mode"], "delta^2 B_PT < 0")
        self.assertEqual(flags["caustic_uncontrolled"], "det(d gamma map)=0 without sheet rule")

    def test_markdown_reports_open_screen(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("S_path Stability Screen", markdown)
        self.assertIn("Lorentz naive invariant indefinite: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
