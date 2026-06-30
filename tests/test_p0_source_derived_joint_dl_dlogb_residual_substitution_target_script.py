from __future__ import annotations

import unittest

from scripts.build_p0_source_derived_joint_dl_dlogb_residual_substitution_target import (
    build_payload,
    render_markdown,
)


class P0SourceDerivedJointDLDlogBResidualSubstitutionTargetTests(unittest.TestCase):
    def test_target_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "source-derived-joint-dl-dlogb-residual-substitution-target-open",
        )
        self.assertFalse(payload["all_rows_source_derived"])
        self.assertFalse(payload["all_rows_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["uses_observational_fit"])

    def test_both_residual_rows_require_joint_identities(self) -> None:
        payload = build_payload()
        rows = {row["sector"]: row for row in payload["residual_substitution_rows"]}

        self.assertEqual(set(rows), {"R_plus", "R_minus"})
        for row in rows.values():
            self.assertIn("same_l_dl_source_law", row["required_identities"])
            self.assertIn("b4vol_source_measure_law", row["required_identities"])
            self.assertIn("falpha_source_law", row["required_identities"])
            self.assertIn("projected_cuu_force_balance", row["required_identities"])
            self.assertIn("K_plus/K_minus", row["same_l_usage"])
            self.assertIn("Q_cross optical projection", row["same_l_usage"])
            self.assertIn("kinetic/Vlasov projection", row["same_l_usage"])
            self.assertFalse(row["closed"])

    def test_forbids_shortcuts_and_vlasov_promotion(self) -> None:
        payload = build_payload()
        text = " ".join(payload["forbidden_shortcuts"])

        self.assertIn("Q_det", text)
        self.assertIn("Q_cross", text)
        self.assertIn("independent optical L", text)
        self.assertIn("fitted Omega", text)
        self.assertIn("Vlasov diagnostic promotion", text)

    def test_markdown_records_joint_gate(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("R_plus", markdown)
        self.assertIn("R_minus", markdown)
        self.assertIn("same_l_dl_source_law", markdown)
        self.assertIn("b4vol_source_measure_law", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
