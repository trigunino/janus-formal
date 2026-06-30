from __future__ import annotations

import unittest

from scripts.build_p0_eft_run7_dirac_spectrum_pairing_audit import build_payload, render_markdown


class P0EFTRun7DiracSpectrumPairingAuditTests(unittest.TestCase):
    def test_pairing_interface_is_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["dirac_spectrum_pairing_interface_ready"])
        self.assertTrue(status["nonzero_pairing_formalized"])

    def test_zero_mode_control_remains_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["zero_mode_control_proved"])
        self.assertFalse(status["aps_pin_global_index_package_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_anticommutator(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("{A_APS, J} = 0", markdown)
        self.assertIn("lambda <-> -lambda", markdown)


if __name__ == "__main__":
    unittest.main()
