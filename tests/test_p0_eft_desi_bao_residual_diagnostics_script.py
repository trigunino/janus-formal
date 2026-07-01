from __future__ import annotations

import unittest

from scripts.build_p0_eft_desi_bao_residual_diagnostics import build_payload


class P0EFTDESIBAOResidualDiagnosticsTests(unittest.TestCase):
    def test_residual_diagnostics_are_computed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "desi-bao-residual-diagnostics-computed")
        self.assertGreater(payload["baseline_no_junction"]["chi2"], 0.0)
        self.assertIn("DM_over_rs", payload["baseline_no_junction"]["by_quantity"])
        self.assertIn("DH_over_rs", payload["baseline_no_junction"]["by_quantity"])

    def test_split_junction_scan_has_best_node(self) -> None:
        best = build_payload()["best_split_junction_scan"]

        self.assertGreater(best["scanned_nodes"], 1)
        self.assertGreater(best["radial_jump"], 0.0)
        self.assertGreater(best["transverse_jump"], 0.0)


if __name__ == "__main__":
    unittest.main()
