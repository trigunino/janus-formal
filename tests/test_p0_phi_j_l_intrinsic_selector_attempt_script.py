from __future__ import annotations

import unittest

from scripts.build_p0_phi_j_l_intrinsic_selector_attempt import build_payload, render_markdown


class P0PhiJLIntrinsicSelectorAttemptTests(unittest.TestCase):
    def test_intrinsic_selector_fixes_toy_family(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "intrinsic-selector-selects-toy-map-new-principle")
        self.assertTrue(payload["intrinsic_selector_fixes_toy_family"])
        self.assertEqual(payload["selected_epsilon"], 0)
        self.assertIn("epsilon: 0", payload["stationarity_solutions"])
        self.assertFalse(payload["prediction_ready"])

    def test_selector_is_not_janus_source_derived(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["source_derived_from_janus"])
        self.assertTrue(payload["new_axiom_risk"])
        self.assertFalse(payload["can_use_as_published_janus_closure"])
        self.assertTrue(payload["can_use_as_candidate_research_principle"])

    def test_rows_distinguish_candidate_principles_from_source_conditions(self) -> None:
        rows = {row["selector"]: row for row in build_payload()["rows"]}

        self.assertTrue(rows["minimal_distortion"]["selects_unique"])
        self.assertFalse(rows["minimal_distortion"]["source_derived"])
        self.assertTrue(rows["harmonic_map_regularizer"]["selects_unique"])
        self.assertFalse(rows["harmonic_map_regularizer"]["source_derived"])
        self.assertFalse(rows["mirror_periodic_boundary"]["selects_unique"])
        self.assertTrue(rows["mirror_periodic_boundary"]["source_derived"])

    def test_acceptance_before_use_keeps_residual_closure_required(self) -> None:
        acceptance = " ".join(build_payload()["acceptance_before_use"])

        self.assertIn("derive the functional from Janus", acceptance)
        self.assertIn("covariance", acceptance)
        self.assertIn("R_plus and R_minus", acceptance)

    def test_markdown_keeps_new_axiom_risk_visible(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Selected epsilon: 0", markdown)
        self.assertIn("Source-derived from Janus: False", markdown)
        self.assertIn("New axiom risk: True", markdown)


if __name__ == "__main__":
    unittest.main()
