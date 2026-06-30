from __future__ import annotations

import unittest

from scripts.build_p0_orbifold_pt_soldering_candidate import build_payload, render_markdown


class P0OrbifoldPTSolderingCandidateTests(unittest.TestCase):
    def test_candidate_is_single_geometric_extension_not_prediction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "orbifold-pt-soldering-candidate-not-source-derived")
        self.assertTrue(payload["new_axiom_candidate"])
        self.assertFalse(payload["source_derived_from_published_janus"])
        self.assertTrue(payload["less_rustine_than_free_spath"])
        self.assertFalse(payload["s_path_added_by_hand"])
        self.assertTrue(payload["same_l_made_structural"])
        self.assertFalse(payload["prediction_ready"])

    def test_geometric_objects_define_orbifold_soldering(self) -> None:
        objects = {row["object"]: row for row in build_payload()["geometric_objects"]}

        self.assertEqual(
            set(objects),
            {
                "double_cover",
                "pt_involution",
                "orbifold_quotient",
                "pt_fixed_locus",
                "solder_connection",
                "solder_holonomy",
                "orbifold_curvature",
            },
        )
        self.assertIn("tau^2=id", objects["pt_involution"]["symbol"])
        self.assertIn("M_tilde / tau", objects["orbifold_quotient"]["symbol"])
        self.assertIn("P exp", objects["solder_holonomy"]["symbol"])

    def test_induced_targets_cover_spath_same_l_cjvj_and_bianchi(self) -> None:
        targets = {row["target"]: row for row in build_payload()["induced_targets"]}

        self.assertEqual(set(targets), {"S_path", "same_L", "C_J/V_J", "PT_boundary", "Bianchi_Noether"})
        self.assertEqual(targets["same_L"]["automatic"], "yes-if-A_PT-unique")
        self.assertIn("derive coefficients", targets["C_J/V_J"]["remaining"])
        self.assertIn("R_plus=0", targets["Bianchi_Noether"]["remaining"])

    def test_acceptance_gates_keep_it_non_rustine(self) -> None:
        gates = " ".join(build_payload()["acceptance_gates"])

        self.assertIn("covariant orbifold action", gates)
        self.assertIn("A_PT Euler equation", gates)
        self.assertIn("same L", gates)
        self.assertIn("observational fit", gates)
        self.assertIn("Q_det/Q_cross", gates)

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Orbifold/PT Soldering Candidate", markdown)
        self.assertIn("Less rustine than free S_path: True", markdown)
        self.assertIn("A_PT Euler equation derived: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
