from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_action_basis_acceptance_filter import (
    build_payload,
    render_markdown,
)


class P0TracefreeHActionBasisAcceptanceFilterTests(unittest.TestCase):
    def test_filter_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "tracefree-h-action-basis-acceptance-filter-open",
        )
        self.assertEqual(payload["candidate_class_count"], 4)
        self.assertTrue(payload["all_fail_janus_provenance"])
        self.assertFalse(payload["any_class_accepted"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_action_basis_candidate_classes_are_echoed(self) -> None:
        rows = {row["candidate_class"]: row for row in build_payload()["filter_rows"]}

        self.assertEqual(
            list(rows),
            [
                "ultralocal invariants",
                "derivative kinetic",
                "linear couplings",
                "BF/GL constraints",
            ],
        )
        self.assertEqual(rows["ultralocal invariants"]["terms"], ["tr_qtf2", "tr_qtf3"])
        self.assertEqual(
            rows["derivative kinetic"]["terms"],
            ["dqtf_kinetic", "dhtf_kinetic"],
        )
        self.assertEqual(
            rows["linear couplings"]["terms"],
            ["qtf_pi_tf", "qtf_weyl", "qtf_phi_sigma"],
        )
        self.assertEqual(rows["BF/GL constraints"]["terms"], ["bf_gl_constraints"])

    def test_acceptance_columns_are_present_and_unaccepted(self) -> None:
        payload = build_payload()
        labels = [column["label"] for column in payload["acceptance_columns"]]

        self.assertEqual(
            labels,
            [
                "Janus provenance",
                "STF EL operator",
                "boundary/gauge",
                "same-L",
                "mirror inverse",
                "ghost/stability",
                "no residual/no determinant",
            ],
        )
        for row in payload["filter_rows"]:
            self.assertFalse(row["janus_provenance"])
            self.assertFalse(row["stf_el_operator"])
            self.assertFalse(row["boundary_gauge"])
            self.assertFalse(row["same_l"])
            self.assertFalse(row["mirror_inverse"])
            self.assertFalse(row["ghost_stability"])
            self.assertTrue(row["no_residual_no_determinant"])
            self.assertFalse(row["accepted"])
            self.assertFalse(row["prediction"])

    def test_best_next_branch_is_derivative_linear_after_provenance(self) -> None:
        branch = build_payload()["best_next_branch"]

        self.assertEqual(branch["classes"], ["derivative kinetic", "linear couplings"])
        self.assertFalse(branch["allowed_now"])
        self.assertIn("source/action provenance", branch["condition"])

    def test_markdown_reports_filter_and_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Action-Basis Acceptance Filter", markdown)
        self.assertIn("ultralocal invariants", markdown)
        self.assertIn("derivative kinetic", markdown)
        self.assertIn("linear couplings", markdown)
        self.assertIn("BF/GL constraints", markdown)
        self.assertIn("Janus provenance", markdown)
        self.assertIn("no residual/no determinant", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("derivative/linear coupling only after source/action provenance", markdown)


if __name__ == "__main__":
    unittest.main()
