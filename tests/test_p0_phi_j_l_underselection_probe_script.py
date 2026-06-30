from __future__ import annotations

import unittest

from scripts.build_p0_phi_j_l_underselection_probe import build_payload, render_markdown


class P0PhiJLUnderselectionProbeTests(unittest.TestCase):
    def test_multiple_local_maps_remain_admissible(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "phi-j-l-underselection-open")
        self.assertTrue(payload["all_candidates_locally_admissible"])
        self.assertTrue(payload["distinct_admissible_maps_exist"])
        self.assertTrue(payload["underselection_proved_for_family"])
        self.assertEqual(
            payload["boundary_selector_probe_status"],
            "boundary-selectors-can-fix-family-but-not-source-supplied",
        )
        self.assertTrue(payload["strong_boundary_selectors_exist"])
        self.assertFalse(payload["strong_boundary_selectors_source_supplied"])
        self.assertFalse(payload["mirror_topology_alone_fixes_unique_map"])
        self.assertEqual(
            payload["intrinsic_selector_attempt_status"],
            "intrinsic-selector-selects-toy-map-new-principle",
        )
        self.assertTrue(payload["intrinsic_selector_fixes_toy_family"])
        self.assertFalse(payload["intrinsic_selector_source_derived"])
        self.assertEqual(
            payload["janus_equations_selector_status"],
            "janus-equations-fix-b4vol-not-phi-without-extra-gauge",
        )
        self.assertTrue(payload["janus_equations_select_b4vol_weight"])
        self.assertFalse(payload["janus_equations_select_phi_without_extra_gauge"])
        self.assertFalse(payload["unique_phi_j_l_selected"])
        self.assertFalse(payload["prediction_ready"])

    def test_candidates_are_invertible_and_distinct(self) -> None:
        payload = build_payload()
        epsilons = {row["epsilon"] for row in payload["candidates"]}
        ranges = {(row["min_jacobian"], row["max_jacobian"]) for row in payload["candidates"]}

        self.assertIn(0.0, epsilons)
        self.assertIn(0.1, epsilons)
        self.assertGreater(len(ranges), 1)
        self.assertTrue(all(row["invertible"] for row in payload["candidates"]))

    def test_local_tests_close_except_unique_selection(self) -> None:
        tests = {row["test"]: row for row in build_payload()["local_tests"]}

        self.assertTrue(tests["integrability"]["closed"])
        self.assertTrue(tests["b4vol_identity"]["closed"])
        self.assertTrue(tests["dl_identity"]["closed"])
        self.assertFalse(tests["unique_selection"]["closed"])

    def test_no_fit_or_scalar_absorption(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["source_boundary_conditions_supplied"])

    def test_markdown_keeps_selector_gap_visible(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Underselection proved for family: True", markdown)
        self.assertIn("Strong boundary selectors source supplied: False", markdown)
        self.assertIn("Intrinsic selector source derived: False", markdown)
        self.assertIn("Janus equations select phi without extra gauge: False", markdown)
        self.assertIn("Unique phi/J/L selected: False", markdown)
        self.assertIn("Remaining Selectors", markdown)


if __name__ == "__main__":
    unittest.main()
