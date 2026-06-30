from __future__ import annotations

import unittest

from scripts.build_p0_eft_run7_dirac_kernel_trivialization_audit import build_payload, render_markdown


class P0EFTRun7DiracKernelTrivializationAuditTests(unittest.TestCase):
    def test_kernel_gap_interface_is_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["dirac_kernel_trivialization_interface_ready"])
        self.assertTrue(status["lichnerowicz_positive_gap_formalized"])
        self.assertTrue(status["zero_mode_control_proved_from_loaded_gap"])

    def test_global_no_fit_still_blocked_by_other_global_requirements(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["aps_pin_global_index_package_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_lichnerowicz_gap(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("A_APS^2", markdown)
        self.assertIn("R_Sigma > 0", markdown)


if __name__ == "__main__":
    unittest.main()
