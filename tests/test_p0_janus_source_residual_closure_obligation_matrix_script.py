from __future__ import annotations

import unittest

from scripts.build_p0_janus_source_residual_closure_obligation_matrix import (
    build_payload,
    render_markdown,
)


class P0JanusSourceResidualClosureObligationMatrixTests(unittest.TestCase):
    def test_matrix_is_written_but_not_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-residual-closure-obligation-matrix-open")
        self.assertTrue(payload["residual_matrix_written"])
        self.assertTrue(payload["residual_row_closure_computed"])
        self.assertTrue(payload["scalar_absorption_forbidden"])
        self.assertFalse(payload["all_required_identities_source_derived"])
        self.assertTrue(payload["all_guardrails_satisfied"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["r_minus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_residual_rows_cover_plus_and_minus_source_obligations(self) -> None:
        payload = build_payload()
        sectors = {row["sector"] for row in payload["residual_rows"]}
        requirements = " ".join(
            requirement
            for row in payload["residual_rows"]
            for requirement in row["requires"]
        )

        self.assertEqual(sectors, {"R_plus", "R_minus"})
        self.assertIn("shared_phi_j_source_selection", requirements)
        self.assertIn("same_l_dl_source_law", requirements)
        self.assertIn("b4vol_source_measure_law", requirements)
        self.assertIn("falpha_source_law", requirements)
        self.assertIn("projected_cuu_force_balance", requirements)

    def test_residual_row_closure_is_mechanical(self) -> None:
        payload = build_payload()

        for row in payload["residual_rows"]:
            expected = (
                all(
                    payload["identity_status"][name]["source_derived"]
                    for name in row["requires"]
                )
                and payload["all_guardrails_satisfied"]
            )
            self.assertEqual(row["closed"], expected)
            self.assertFalse(row["required_identities_source_derived"])
            self.assertTrue(row["guardrails_satisfied"])

    def test_identity_status_keeps_source_derivation_missing(self) -> None:
        payload = build_payload()
        missing = set(payload["missing_source_identities"])

        self.assertIn("same_l_dl_source_law", missing)
        self.assertIn("shared_phi_j_source_selection", missing)
        self.assertIn("b4vol_source_measure_law", missing)
        self.assertIn("projected_cuu_force_balance", missing)
        self.assertNotIn("diagnostic_non_promotion", missing)
        self.assertTrue(all(not row["source_derived"] for row in payload["identity_status"].values()))
        self.assertEqual(
            payload["identity_status"]["shared_phi_j_source_selection"]["artifact"],
            "p0_shared_phi_j_source_selection_gate",
        )
        self.assertEqual(
            payload["identity_status"]["same_l_dl_source_law"]["artifact"],
            "p0_source_derived_same_l_dl_residual_closure_target",
        )
        self.assertEqual(
            payload["identity_status"]["b4vol_source_measure_law"]["artifact"],
            "p0_dlogb4vol_source_slice_lapse_obligation_ledger",
        )
        self.assertEqual(
            payload["identity_status"]["falpha_source_law"]["artifact"],
            "p0_falpha_source_law_obligation_ledger",
        )
        self.assertEqual(
            payload["identity_status"]["projected_cuu_force_balance"]["artifact"],
            "p0_projected_cuu_action_pullback_bridge_ledger",
        )
        self.assertTrue(payload["guardrail_status"]["diagnostic_non_promotion"]["satisfied"])
        self.assertEqual(payload["failed_guardrails"], [])

    def test_markdown_forbids_qdet_qcross_absorption(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Q_det", markdown)
        self.assertIn("Q_cross", markdown)
        self.assertIn("R_plus", markdown)
        self.assertIn("R_minus", markdown)
        self.assertIn("Guardrail Status", markdown)
        self.assertIn("Residual row closure computed: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
