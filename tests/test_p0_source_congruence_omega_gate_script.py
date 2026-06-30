from __future__ import annotations

import unittest

from scripts.build_p0_source_congruence_omega_gate import build_payload, render_markdown


class P0SourceCongruenceOmegaGateTests(unittest.TestCase):
    def test_gate_is_open_bounded_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-congruence-omega-gate-open")
        self.assertTrue(payload["geodesic_route_allowed"])
        self.assertTrue(payload["cross_force_route_allowed"])
        self.assertTrue(payload["transported_tetrad_required"])
        self.assertTrue(payload["same_l_omega_required"])
        self.assertFalse(payload["fit_choice_allowed"])
        self.assertTrue(payload["no_fit"])
        self.assertFalse(payload["source_derivation_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["prediction_claim"])

    def test_equations_include_geodesic_cross_force_and_tetrad_relation(self) -> None:
        text = " ".join(row["name"] + row["form"] + row["status"] for row in build_payload()["equations"])

        self.assertIn("Omega_alpha=(D_alpha L)L^{-1}", text)
        self.assertIn("Omega_u=u^alpha Omega_alpha", text)
        self.assertIn("u^beta D_beta u^alpha=0", text)
        self.assertIn("f_cross^alpha", text)
        self.assertIn("D_u e_A=Omega_u", text)
        self.assertIn("Omega_u{}^A{}_B u^B=0", text)

    def test_same_l_omega_k_qcross_and_blockers_are_explicit(self) -> None:
        payload = build_payload()
        blockers = " ".join(payload["blockers"])
        equations = " ".join(row["form"] for row in payload["equations"])

        self.assertTrue(payload["k_qcross_required"])
        self.assertFalse(payload["k_qcross_closed"])
        self.assertIn("same L/Omega", equations)
        self.assertIn("K transport", equations)
        self.assertIn("Q_cross", equations)
        self.assertIn("source equations", blockers)
        self.assertIn("post-hoc fitting", blockers)

    def test_routes_are_alternatives_and_unclosed(self) -> None:
        routes = {row["route"]: row for row in build_payload()["routes"]}

        self.assertIn("geodesic", routes)
        self.assertIn("cross_force", routes)
        self.assertIn("u.D u=0", routes["geodesic"]["claim"])
        self.assertIn("f_cross", routes["cross_force"]["claim"])
        self.assertTrue(all(not row["closed"] for row in routes.values()))

    def test_markdown_renders_prediction_false_and_no_fit(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("| name | form | status |", markdown)
        self.assertIn("Fit choice allowed: False", markdown)
        self.assertIn("No fit: True", markdown)
        self.assertIn("Prediction claim: False", markdown)


if __name__ == "__main__":
    unittest.main()
