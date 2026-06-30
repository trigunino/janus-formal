from __future__ import annotations

import unittest

from scripts.build_p0_integrability_closure_route import build_payload, render_markdown


class P0IntegrabilityClosureRouteTests(unittest.TestCase):
    def test_route_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "integrability-closure-route-open")
        self.assertFalse(payload["source_derived_curvature_rule"])
        self.assertFalse(payload["source_derived_path_rule"])
        self.assertTrue(payload["same_l_for_k_and_qcross"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_relative_connection_names_cartan_curvature_and_dl(self) -> None:
        rel = build_payload()["relative_connection"]
        text = " ".join(rel.values())

        self.assertIn("Omega_alpha", rel["object"])
        self.assertIn("R_Omega=d Omega+Omega wedge Omega", text)
        self.assertIn("D_alpha L", rel["dl_equation"])
        self.assertIn("eta-antisymmetric", rel["lorentz_condition"])

    def test_branch_rules_cover_flat_holonomy_and_curved_cases(self) -> None:
        branches = {rule["branch"]: rule for rule in build_payload()["branch_rules"]}

        self.assertEqual(
            set(branches),
            {"flat_pure_gauge", "flat_nontrivial_holonomy", "curved_relative_holonomy"},
        )
        self.assertIn("R_Omega=0", branches["flat_pure_gauge"]["condition"])
        self.assertIn("holonomy", branches["flat_nontrivial_holonomy"]["global_result"])
        self.assertIn("R_Omega!=0", branches["curved_relative_holonomy"]["condition"])
        self.assertIn("same for K and Q_cross", branches["curved_relative_holonomy"]["path_rule"])

    def test_frobenius_checks_require_curvature_path_rule(self) -> None:
        checks = " ".join(build_payload()["frobenius_checks"])

        self.assertIn("[D_alpha,D_beta]L", checks)
        self.assertIn("local path-independence", checks)
        self.assertIn("curvature/path rule", checks)
        self.assertIn("Lorentz-admissible", checks)

    def test_closure_obligations_keep_source_derived_same_l_and_not_ready(self) -> None:
        payload = build_payload()
        obligations = " ".join(payload["closure_obligations"])

        self.assertIn("Janus source equations", obligations)
        self.assertIn("pure gauge, flat holonomy, or curved holonomy", obligations)
        self.assertIn("same L and the same path/family rule", obligations)
        self.assertIn("D(BK)=0", obligations)
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_renders_required_guardrails(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Source-derived curvature rule: False", markdown)
        self.assertIn("Same L for K and Q_cross: True", markdown)
        self.assertIn("## Frobenius/Integrability Checks", markdown)


if __name__ == "__main__":
    unittest.main()
