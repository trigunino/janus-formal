from __future__ import annotations

import unittest

from scripts.build_p0_zero_axiom_closure_decision_gate import build_payload, render_markdown


class P0ZeroAxiomClosureDecisionGateTests(unittest.TestCase):
    def test_decision_gate_blocks_prediction_without_adopting_axiom(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "zero-axiom-closure-decision-open")
        self.assertTrue(payload["route_c_bounded_underselection_closed"])
        self.assertFalse(payload["route_c_indirect_source_found"])
        self.assertFalse(payload["route_c_action_noether_path_rule_derived"])
        self.assertFalse(payload["route_c_pt_path_rule_selected"])
        self.assertFalse(payload["route_c_pt_selector_derivation_closed"])
        self.assertTrue(payload["route_c_pt_only_no_selector_closed"])
        self.assertFalse(payload["route_c_ordered_path_action_source_found"])
        self.assertTrue(payload["route_c_ordered_path_source_no_go_closed"])
        self.assertTrue(payload["route_c_minimal_spath_extension_declared"])
        self.assertFalse(payload["route_c_minimal_spath_prediction_ready"])
        self.assertTrue(payload["route_c_spath_el_formally_derived"])
        self.assertFalse(payload["route_c_spath_el_prediction_ready"])
        self.assertTrue(payload["route_c_spath_lorentz_variation_formalized"])
        self.assertFalse(payload["route_c_spath_lorentz_prediction_ready"])
        self.assertTrue(payload["route_c_spath_same_l_contract_written"])
        self.assertFalse(payload["route_c_spath_same_l_physics_closed"])
        self.assertTrue(payload["route_c_spath_stability_screen_written"])
        self.assertFalse(payload["route_c_spath_stability_closed"])
        self.assertTrue(payload["route_c_spath_bianchi_noether_gate_written"])
        self.assertTrue(payload["route_c_spath_metric_stress_variation_written"])
        self.assertFalse(payload["route_c_spath_metric_stress_variation_closed"])
        self.assertFalse(payload["route_c_spath_bianchi_noether_closed"])
        self.assertTrue(payload["route_c_pt_two_path_counterexample_survives"])
        self.assertTrue(payload["route_d_formal_stf_only"])
        self.assertTrue(payload["route_d_known_non_source_stf_excluded"])
        self.assertFalse(payload["route_d_full_stf_no_go_proved"])
        self.assertFalse(payload["zero_axiom_closure_available"])
        self.assertFalse(payload["new_axiom_adopted"])
        self.assertTrue(payload["extension_needed_for_prediction_if_no_new_source"])
        self.assertFalse(payload["prediction_ready"])

    def test_allowed_and_forbidden_next_are_explicit(self) -> None:
        payload = build_payload()

        self.assertIn("find a Janus source for the holonomy path rule", payload["allowed_next_without_axiom"])
        self.assertIn("derive an accepted Janus STF source/action operator", payload["allowed_next_without_axiom"])
        self.assertIn("choose a path family by convenience", payload["forbidden_next"])
        self.assertIn("fit lensing residuals to select L", payload["forbidden_next"])

    def test_markdown_reports_decision(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Zero-Axiom Closure Decision", markdown)
        self.assertIn("Route C PT path rule selected: False", markdown)
        self.assertIn("Route C PT selector derivation closed: False", markdown)
        self.assertIn("Route C PT-only no-selector closed: True", markdown)
        self.assertIn("Route C ordered path action source found: False", markdown)
        self.assertIn("Route C ordered path source no-go closed: True", markdown)
        self.assertIn("Route C minimal S_path extension declared: True", markdown)
        self.assertIn("Route C minimal S_path prediction ready: False", markdown)
        self.assertIn("Route C S_path EL formally derived: True", markdown)
        self.assertIn("Route C S_path EL prediction ready: False", markdown)
        self.assertIn("Route C S_path Lorentz variation formalized: True", markdown)
        self.assertIn("Route C S_path Lorentz prediction ready: False", markdown)
        self.assertIn("Route C S_path same-L contract written: True", markdown)
        self.assertIn("Route C S_path same-L physics closed: False", markdown)
        self.assertIn("Route C S_path stability screen written: True", markdown)
        self.assertIn("Route C S_path stability closed: False", markdown)
        self.assertIn("Route C S_path Bianchi/Noether gate written: True", markdown)
        self.assertIn("Route C S_path metric-stress variation written: True", markdown)
        self.assertIn("Route C S_path metric-stress variation closed: False", markdown)
        self.assertIn("Route C S_path Bianchi/Noether closed: False", markdown)
        self.assertIn("Zero-axiom closure available: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
