from __future__ import annotations

import unittest

from scripts.build_p0_dlogb4vol_source_slice_lapse_obligation_ledger import (
    build_payload,
    render_markdown,
)


class P0DlogB4volSourceSliceLapseObligationLedgerTests(unittest.TestCase):
    def test_ledger_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-slice-lapse-obligation-ledger-open")
        self.assertTrue(payload["diagnostic_product_rule_only"])
        self.assertTrue(payload["jacobian_lapse_slice_identity_written"])
        self.assertTrue(payload["jacobian_lapse_slice_identity_numeric_closes"])
        self.assertTrue(payload["mirror_reciprocity_numeric_closes"])
        self.assertFalse(payload["source_selected_measure_found"])
        self.assertFalse(payload["source_slice_lapse_obligations_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_required_identity_types_are_exhaustive_for_current_gate(self) -> None:
        types = {row["required_identity_type"] for row in build_payload()["obligation_rows"]}

        self.assertEqual(
            types,
            {
                "source-determinant",
                "slice-determinant",
                "lapse-reinsertion",
                "density-transport",
                "velocity-tetrad",
                "mirror-reciprocity",
                "jacobian-lapse-slice",
            },
        )

    def test_forbidden_operations_prevent_rustines(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_operations"])

        self.assertTrue(payload["qdet_qcross_absorption_forbidden"])
        self.assertTrue(payload["b4vol_v3_dust_conflation_forbidden"])
        self.assertTrue(payload["branch_selection_is_not_closure"])
        self.assertIn("Q_det", forbidden)
        self.assertIn("Q_cross", forbidden)
        self.assertIn("B_4vol/V3_dust", forbidden)

    def test_markdown_names_lapse_slice_and_mirror(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("lapse-reinsertion", markdown)
        self.assertIn("slice-determinant", markdown)
        self.assertIn("mirror-reciprocity", markdown)
        self.assertIn("Jacobian/lapse/slice identity numeric closes: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
