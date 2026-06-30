from __future__ import annotations

import unittest

from scripts.build_p0_eft_pin_structure_conditional import build_payload, render_markdown


class P0EFTPinStructureConditionalTests(unittest.TestCase):
    def test_pin_structure_fixes_qA_conditionally(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["pin_structure_axiom_written"])
        self.assertTrue(status["pin_minus_selected_by_anomaly_filter"])
        self.assertFalse(status["aps_index_calculation_done"])
        self.assertTrue(status["q_A_fixed_conditionally"])
        self.assertFalse(status["metric_only_derivation"])
        self.assertFalse(status["prediction_ready"])

    def test_axiom_is_not_fit_but_additional_geometry(self) -> None:
        axiom = build_payload()["axiom"]

        self.assertEqual(axiom["id"], "A_PinPTSpinStructure")
        self.assertFalse(axiom["source_derived_from_metric"])
        self.assertTrue(axiom["selected_by_global_anomaly_cancellation"])
        self.assertFalse(axiom["aps_index_calculation_done"])
        self.assertFalse(axiom["observational_fit"])

    def test_pin_minus_is_selected_by_health_filter(self) -> None:
        options = {row["structure"]: row for row in build_payload()["pin_options"]}

        self.assertFalse(options["Pin+"]["healthy"])
        self.assertEqual(options["Pin+"]["global_parity_anomaly"], "nonzero")
        self.assertTrue(options["Pin-"]["healthy"])
        self.assertEqual(options["Pin-"]["q_A"], "sign(Sigma)/sqrt(6)")

    def test_implications_chain_to_fixed_heat_kernel_target(self) -> None:
        implications = " ".join(build_payload()["implications"])

        self.assertIn("chiral holonomy", implications)
        self.assertIn("fixed q_A/q_T", implications)

    def test_markdown_keeps_additional_data_warning(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("APS/index anomaly calculation", markdown)
        self.assertIn("Pin-", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
