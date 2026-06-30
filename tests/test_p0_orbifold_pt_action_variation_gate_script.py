from __future__ import annotations

import unittest

from scripts.build_p0_orbifold_pt_action_variation_gate import build_payload, render_markdown


class P0OrbifoldPTActionVariationGateTests(unittest.TestCase):
    def test_action_skeleton_is_written_but_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "orbifold-pt-action-variation-gate-open")
        self.assertTrue(payload["orbifold_action_written"])
        self.assertTrue(payload["a_pt_euler_equation_written"])
        self.assertFalse(payload["a_pt_euler_equation_derived_from_accepted_source"])
        self.assertTrue(payload["same_l_structural_if_unique_connection"])
        self.assertFalse(payload["cj_vj_coefficients_derived"])
        self.assertFalse(payload["defect_boundary_law_derived"])
        self.assertFalse(payload["k_plus_k_minus_derived"])
        self.assertFalse(payload["split_noether_bianchi_proved"])
        self.assertFalse(payload["prediction_ready"])

    def test_action_terms_cover_solder_defect_matter_and_sectors(self) -> None:
        terms = {row["term"]: row for row in build_payload()["action_terms"]}

        self.assertEqual(
            set(terms),
            {
                "sector_einstein_hilbert",
                "solder_yang_mills",
                "defect_boundary",
                "matter_solder_coupling",
            },
        )
        self.assertIn("F_PT", terms["solder_yang_mills"]["density"])
        self.assertIn("Sigma_PT", terms["defect_boundary"]["density"])
        self.assertIn("L_gamma", terms["matter_solder_coupling"]["density"])

    def test_variations_include_a_pt_metric_boundary_and_noether(self) -> None:
        rows = {row["variation"]: row for row in build_payload()["variation_rows"]}

        self.assertEqual(
            set(rows),
            {
                "delta_A_PT",
                "delta_g_plus",
                "delta_g_minus",
                "delta_boundary_Sigma_PT",
                "orbifold_noether",
            },
        )
        self.assertIn("D_A *F_PT", rows["delta_A_PT"]["formal_equation"])
        self.assertTrue(all(row["derived_formally"] for row in rows.values()))
        self.assertTrue(all(not row["closed_for_prediction"] for row in rows.values()))

    def test_induced_quantities_cover_same_l_spath_cjvj(self) -> None:
        quantities = {row["quantity"]: row for row in build_payload()["induced_quantities"]}

        self.assertEqual(set(quantities), {"same_L", "S_path", "C_J/V_J"})
        self.assertIn("P exp", quantities["same_L"]["definition"])
        self.assertIn("holonomy", quantities["S_path"]["definition"])
        self.assertIn("F_PT", quantities["C_J/V_J"]["definition"])

    def test_markdown_reports_open_gate(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Orbifold/PT Action Variation Gate", markdown)
        self.assertIn("A_PT Euler equation written: True", markdown)
        self.assertIn("C_J/V_J coefficients derived: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
