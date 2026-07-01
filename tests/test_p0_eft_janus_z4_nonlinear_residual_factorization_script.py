from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_nonlinear_residual_factorization import build_payload, write_reports


class P0EFTJanusZ4NonlinearResidualFactorizationScriptTests(unittest.TestCase):
    def test_residual_pair_reduces_to_single_common_obstruction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["factorization_residual"], "Matrix([[0], [0]])")
        self.assertEqual(payload["weighted_consistency"], "0")
        self.assertTrue(payload["residual_factorization_ready"])
        self.assertFalse(payload["obstruction_vanishing_derived"])
        self.assertFalse(payload["full_action_variation_closed"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_nonlinear_residual_factorization.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_nonlinear_residual_factorization.md").exists())
        self.assertIn("O_nl = 0", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
