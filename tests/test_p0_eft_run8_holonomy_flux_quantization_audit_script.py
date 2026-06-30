from __future__ import annotations

import unittest

from scripts.build_p0_eft_run8_holonomy_flux_quantization_audit import build_payload, render_markdown


class P0EFTRun8HolonomyFluxQuantizationAuditTests(unittest.TestCase):
    def test_flux_interface_is_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run8_holonomy_flux_interface_ready"])
        self.assertTrue(status["flux_to_branch_index_arrow_formalized"])

    def test_branch_indices_remain_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["flux_quantization_condition_proved"])
        self.assertFalse(status["positive_branch_index_two_proved"])
        self.assertFalse(status["orbifold_cover_global_theorem_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_flux_integral(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("omega^{ab}", markdown)
        self.assertIn("positive branch index 2", markdown)


if __name__ == "__main__":
    unittest.main()
