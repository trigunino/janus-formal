from __future__ import annotations

import unittest

from scripts.build_p0_route_c_ordered_path_action_source_derivation_gate import (
    build_payload,
    render_markdown,
)


class P0RouteCOrderedPathActionSourceDerivationGateTests(unittest.TestCase):
    def test_final_source_pass_finds_no_ordered_path_action(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "ordered-path-action-source-derivation-gate-bounded-no-go")
        self.assertEqual(payload["source_count"], 4)
        self.assertEqual(payload["accepted_source_count"], 0)
        self.assertFalse(payload["ordered_path_action_source_found"])
        self.assertFalse(payload["zero_axiom_derivation_available"])
        self.assertTrue(payload["bounded_source_no_go_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_sources_cover_m15_m29_m30_m31(self) -> None:
        rows = {row["source"]: row for row in build_payload()["source_rows"]}

        self.assertEqual(set(rows), {"M15", "M29", "M30", "M31"})
        self.assertTrue(rows["M15"]["has_action_or_symmetry_terms"])
        self.assertTrue(rows["M29"]["has_transport_geometry_terms"])
        self.assertTrue(rows["M30"]["has_transport_geometry_terms"])
        self.assertTrue(rows["M31"]["has_action_or_symmetry_terms"])
        self.assertTrue(all(not row["s_path_source_found"] for row in rows.values()))
        self.assertTrue(all(not row["forces_ordered_path_rule"] for row in rows.values()))

    def test_no_shortcut_sources_are_promoted(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["coupled_action_forces_ordered_path_rule"])
        self.assertFalse(payload["geodesics_force_ordered_path_rule"])
        self.assertFalse(payload["symmetries_force_ordered_path_rule"])
        self.assertFalse(payload["pt_bridge_forces_cosmological_same_l"])
        self.assertEqual(payload["minimal_extension_object"], "S_path[gamma,L; g_plus, g_minus, PT]")
        self.assertTrue(payload["clean_extension_next_recommended_if_no_new_source"])

    def test_markdown_reports_bounded_no_go(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Ordered Path Action Source Derivation", markdown)
        self.assertIn("Ordered path action source found: False", markdown)
        self.assertIn("Bounded source no-go closed: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
