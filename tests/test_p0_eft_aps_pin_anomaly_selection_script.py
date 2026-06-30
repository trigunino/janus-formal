from __future__ import annotations

import unittest

from scripts.build_p0_eft_aps_pin_anomaly_selection import build_payload, render_markdown


class P0EFTAPSPinAnomalySelectionTests(unittest.TestCase):
    def test_aps_map_is_open_not_proved(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["aps_selection_map_written"])
        self.assertFalse(status["dirac_operator_domain_defined"])
        self.assertFalse(status["eta_invariant_computed"])
        self.assertTrue(status["pin_minus_selected_conditionally"])
        self.assertFalse(status["pin_minus_selected_proved"])
        self.assertFalse(status["prediction_ready"])

    def test_pin_table_rejects_pin_plus_conditionally(self) -> None:
        table = {row["pin"]: row for row in build_payload()["pin_table"]}

        self.assertFalse(table["Pin+"]["accepted"])
        self.assertEqual(table["Pin+"]["eta_anomaly"], "nonzero_mod2")
        self.assertTrue(table["Pin-"]["accepted"])
        self.assertEqual(table["Pin-"]["eta_anomaly"], "zero_mod2")

    def test_obligations_include_operator_domain_and_eta(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("operator and its domain", obligations)
        self.assertIn("eta invariant", obligations)
        self.assertIn("q_A", obligations)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("pin_minus_selected_proved: False", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
