from __future__ import annotations

import unittest

from scripts.build_p0_falpha_source_law_obligation_ledger import build_payload, render_markdown


class P0FalphaSourceLawObligationLedgerTests(unittest.TestCase):
    def test_ledger_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "falpha-source-law-obligation-ledger-open")
        self.assertTrue(payload["obligations_written"])
        self.assertFalse(payload["source_law_derivation_found"])
        self.assertTrue(payload["flow_rows_conditionally_reduced"])
        self.assertTrue(payload["jacobian_tetrad_identity_written"])
        self.assertTrue(payload["jacobian_tetrad_identity_numeric_closes"])
        self.assertFalse(payload["source_selected_jacobian_found"])
        self.assertTrue(payload["minimal_gauge_declared"])
        self.assertFalse(payload["minimal_gauge_promoted"])
        self.assertFalse(payload["all_falpha_components_source_fixed"])
        self.assertFalse(payload["falpha_source_derived"])
        self.assertFalse(payload["source_law_obligations_closed"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_obligations_cover_source_flow_free_and_mirror_rows(self) -> None:
        obligations = {row["obligation"] for row in build_payload()["obligation_rows"]}

        self.assertIn("source_generator", obligations)
        self.assertIn("lorentz_generator", obligations)
        self.assertIn("flow_projection", obligations)
        self.assertIn("jacobian_tetrad_identity", obligations)
        self.assertIn("transverse_free_components", obligations)
        self.assertIn("minimal_gauge_not_source_law", obligations)
        self.assertIn("mirror_inverse", obligations)

    def test_forbidden_operations_prevent_fitted_falpha(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_operations"])

        self.assertFalse(payload["all_falpha_obligations_source_closed"])
        self.assertIn("minimal-gauge F_alpha", forbidden)
        self.assertIn("transverse F_alpha", forbidden)
        self.assertIn("fit F_alpha", forbidden)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Jacobian/tetrad identity numeric closes: True", markdown)
        self.assertIn("source law", markdown)


if __name__ == "__main__":
    unittest.main()
