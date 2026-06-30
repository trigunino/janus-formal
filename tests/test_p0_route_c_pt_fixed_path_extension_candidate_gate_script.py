from __future__ import annotations

import unittest

from scripts.build_p0_route_c_pt_fixed_path_extension_candidate_gate import (
    build_payload,
    render_markdown,
)


class P0RouteCPtFixedPathExtensionCandidateGateTests(unittest.TestCase):
    def test_pt_extension_candidate_is_not_adopted(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "pt-fixed-path-extension-candidate-not-adopted")
        self.assertTrue(payload["pt_extension_candidate_written"])
        self.assertFalse(payload["pt_extension_adopted"])
        self.assertFalse(payload["zero_axiom_source_derived"])
        self.assertTrue(payload["new_axiom_risk"])
        self.assertFalse(payload["can_be_used_for_prediction_now"])
        self.assertFalse(payload["prediction_ready"])

    def test_requirements_cover_same_l_no_fit_and_traceability(self) -> None:
        requirements = {row["requirement"] for row in build_payload()["rows"]}

        self.assertIn("pt_invariant_path_functional", requirements)
        self.assertIn("same_l_transport_stack", requirements)
        self.assertIn("two_path_noncommuting_resolution", requirements)
        self.assertIn("source_traceability", requirements)
        self.assertTrue(build_payload()["requires_no_fit"])
        self.assertTrue(build_payload()["forbids_qdet_qcross_absorption"])

    def test_markdown_reports_candidate_not_prediction(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("PT-Fixed Path Extension Candidate", markdown)
        self.assertIn("PT extension adopted: False", markdown)
        self.assertIn("Can be used for prediction now: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
