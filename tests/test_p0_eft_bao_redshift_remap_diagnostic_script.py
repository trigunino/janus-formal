from __future__ import annotations

import unittest

from scripts.build_p0_eft_bao_redshift_remap_diagnostic import scan_remap


class P0EFTBAORedshiftRemapDiagnosticTests(unittest.TestCase):
    def test_redshift_remap_scan_runs(self) -> None:
        payload = scan_remap()

        self.assertEqual(payload["status"], "bao-redshift-remap-diagnostic-computed")
        self.assertGreater(len(payload["rows"]), 1)
        self.assertIn("best", payload)

    def test_best_has_radial_and_transverse_powers(self) -> None:
        best = scan_remap()["best"]

        self.assertIn("radial_power", best)
        self.assertIn("transverse_power", best)


if __name__ == "__main__":
    unittest.main()
