from __future__ import annotations

import unittest

from scripts.build_p0_eft_desi_bao_final_holst_gate import build_payload


class P0EFTDESIBAOFinalHolstGateTests(unittest.TestCase):
    def test_final_bao_gate_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "desi-bao-holst-diagnostic-closed-cmb-transfer-open")
        self.assertTrue(payload["passes_desi_bao_shape_gate"])
        self.assertTrue(payload["is_no_fit_bao_likelihood"])

    def test_cmb_stays_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["is_full_cmb_ready"])
        self.assertIn("Direct CMB", payload["remaining_obligation"])


if __name__ == "__main__":
    unittest.main()
