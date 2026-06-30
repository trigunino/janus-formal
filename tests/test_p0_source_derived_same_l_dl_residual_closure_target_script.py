from __future__ import annotations

import unittest

from scripts.build_p0_source_derived_same_l_dl_residual_closure_target import (
    build_payload,
    render_markdown,
)


class P0SourceDerivedSameLDLResidualClosureTargetTests(unittest.TestCase):
    def test_target_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-derived-same-l-dl-closure-target-open")
        self.assertFalse(payload["source_derived"])
        self.assertFalse(payload["same_l_closed"])
        self.assertFalse(payload["dl_closed"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["r_minus_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertEqual(
            payload["spin_connection_identity_artifact"],
            "p0_same_l_spin_connection_transport_identity_gate",
        )
        self.assertTrue(payload["spin_connection_identity_algebra_closed"])
        self.assertFalse(payload["spin_connection_identity_source_selected"])

    def test_target_rows_cover_same_l_dl_qcross_and_both_residuals(self) -> None:
        rows = {row["obligation"] for row in build_payload()["target_rows"]}

        self.assertIn("same_l_for_k_qcross_kinetics", rows)
        self.assertIn("dl_source_law", rows)
        self.assertIn("lorentz_tetrad_compatibility", rows)
        self.assertIn("r_plus_substitution", rows)
        self.assertIn("r_minus_substitution", rows)

    def test_dl_row_uses_spin_connection_identity_then_source_selection(self) -> None:
        rows = {row["obligation"]: row for row in build_payload()["target_rows"]}

        self.assertIn("partial_alpha L+omega_s,alpha L-L omega_o,alpha", rows["dl_source_law"]["source_requirement"])
        self.assertIn("source-selects L/Omega", rows["dl_source_law"]["source_requirement"])
        self.assertFalse(rows["dl_source_law"]["source_derived"])

    def test_no_row_is_source_derived_yet(self) -> None:
        rows = build_payload()["target_rows"]

        self.assertTrue(all(not row["source_derived"] for row in rows))
        self.assertTrue(all(not row["closed"] for row in rows))

    def test_markdown_forbids_independent_l_and_scalar_absorption(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("no separate L for K and Q_cross", markdown)
        self.assertIn("Q_det", markdown)
        self.assertIn("Q_cross", markdown)
        self.assertIn("Spin-connection identity algebra closed: True", markdown)
        self.assertIn("Spin-connection identity source selected: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
