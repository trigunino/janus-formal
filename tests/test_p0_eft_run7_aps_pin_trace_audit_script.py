from __future__ import annotations

import unittest

from scripts.build_p0_eft_run7_aps_pin_trace_audit import build_payload, render_markdown


class P0EFTRun7APSPinTraceAuditTests(unittest.TestCase):
    def test_run7_freezes_numeric_and_data(self) -> None:
        frozen = build_payload()["frozen_sectors"]

        self.assertEqual(frozen["numeric_solver"], "untouched")
        self.assertEqual(frozen["sdss_eboss_tables"], "untouched")

    def test_aps_closes_eta_conditionally_not_global_no_fit(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run7_aps_pin_interface_ready"])
        self.assertTrue(status["dirac_spectrum_pairing_interface_ready"])
        self.assertTrue(status["dirac_kernel_trivialization_interface_ready"])
        self.assertTrue(status["zero_mode_control_proved_from_loaded_gap"])
        self.assertTrue(status["aps_pin_global_index_package_proved"])
        self.assertTrue(status["eta_H_no_fit_ready_conditionally_on_APS"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_global_index_package(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("apsPinIndexPackageClosed", markdown)
        self.assertIn("P0EFTAPSPinGlobalIndexClosure", markdown)
        self.assertIn("P0EFTAPSPinDiracKernelTrivialization", markdown)
        self.assertIn("eta_H + 2 = 0", markdown)


if __name__ == "__main__":
    unittest.main()
