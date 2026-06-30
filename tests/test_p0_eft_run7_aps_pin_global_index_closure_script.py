from __future__ import annotations

import unittest

from scripts.build_p0_eft_run7_aps_pin_global_index_closure import build_payload, render_markdown


class P0EFTRun7APSPinGlobalIndexClosureTests(unittest.TestCase):
    def test_aps_global_index_closure_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run7_aps_pin_global_index_closure_ready"])
        self.assertTrue(status["aps_pin_global_index_package_proved"])
        self.assertTrue(status["eta_H_no_fit_ready"])

    def test_no_fit_waits_for_master_lock(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_global_index(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("P0EFTAPSPinGlobalIndexClosure", markdown)
        self.assertIn("apsGlobalIndexClosed", markdown)
        self.assertIn("apsPinIndexPackageClosed", markdown)


if __name__ == "__main__":
    unittest.main()
