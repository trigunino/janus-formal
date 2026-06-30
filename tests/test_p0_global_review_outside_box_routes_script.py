from __future__ import annotations

import unittest

from scripts.build_p0_global_review_outside_box_routes import build_payload


class P0GlobalReviewOutsideBoxRoutesTests(unittest.TestCase):
    def test_review_is_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "review-complete-outside-routes-open")
        self.assertFalse(payload["published_janus_closed"])
        self.assertFalse(payload["extension_axiom_adopted"])
        self.assertFalse(payload["anti_rustine_gate_passed"])
        self.assertFalse(payload["prediction_ready"])

    def test_open_blockers_keep_p0_dynamic_bianchi_and_matter(self) -> None:
        blockers = {row["blocker"]: row for row in build_payload()["open_blockers"]}

        self.assertIn("dynamic_phi_l_selection", blockers)
        self.assertIn("full_bianchi_residuals", blockers)
        self.assertIn("non_dust_matter", blockers)
        self.assertEqual(blockers["dynamic_phi_l_selection"]["severity"], "P0")

    def test_outside_box_routes_include_non_axiom_and_no_go_paths(self) -> None:
        routes = {row["route"]: row for row in build_payload()["outside_box_routes"]}

        self.assertIn("integrability-first", routes)
        self.assertIn("optimal-transport-map", routes)
        self.assertIn("BF-or-connection-constraint", routes)
        self.assertIn("kinetic-sheet-limit", routes)
        self.assertIn("no-go theorem", routes)
        self.assertIn("source-compatible", routes["integrability-first"]["classification"])
        self.assertIn("new-principle", routes["optimal-transport-map"]["classification"])

    def test_active_experiment_artifacts_include_integrability_and_no_go(self) -> None:
        artifacts = set(build_payload()["active_experiment_artifacts"])

        self.assertIn("p0_integrability_first_phi_l_selection", artifacts)
        self.assertIn("p0_integrability_first_equation_system", artifacts)
        self.assertIn("p0_integrability_regular_patch_toy_solver", artifacts)
        self.assertIn("p0_local_phi_scouple_no_go_target", artifacts)
        self.assertIn("p0_local_phi_scouple_symbolic_restricted_audit", artifacts)


if __name__ == "__main__":
    unittest.main()
