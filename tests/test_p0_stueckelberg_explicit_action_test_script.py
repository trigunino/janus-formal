from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_explicit_action_test import build_payload, render_markdown


class P0StueckelbergExplicitActionTestTests(unittest.TestCase):
    def test_explicit_action_is_conditional_not_physics_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "explicit-action-conditional-pass-open")
        self.assertTrue(payload["action_written"])
        self.assertTrue(payload["defines_k_plus_k_minus"])
        self.assertTrue(payload["defines_map_equations_formally"])
        self.assertTrue(payload["split_noether_conditional"])
        self.assertFalse(payload["unconditional_closure_proved"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_action_terms_include_both_pulled_back_couplings(self) -> None:
        terms = " ".join(row["term"] for row in build_payload()["action_terms"])

        self.assertIn("phi^*g_minus", terms)
        self.assertIn("phi_*g_plus", terms)
        self.assertIn("L^T eta L", terms)

    def test_variations_define_k_map_and_split_noether(self) -> None:
        variations = " ".join(row["variation"] + " " + row["gives"] for row in build_payload()["variation_results"])

        self.assertIn("delta g_plus K_plus", variations)
        self.assertIn("delta g_minus K_minus", variations)
        self.assertIn("delta phi E_phi", variations)
        self.assertIn("delta L E_L", variations)
        self.assertIn("split Noether", variations)

    def test_blockers_keep_axiom_open(self) -> None:
        blockers = " ".join(build_payload()["blockers"])

        self.assertIn("Phi/Phi_bar are arbitrary", blockers)
        self.assertIn("overconstrain phi/L", blockers)
        self.assertIn("before observations", blockers)

    def test_markdown_reports_new_axiom(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("New axiom: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
