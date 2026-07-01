from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_weyl_source_equation import build_payload


class P0EFTCMBWeylSourceEquationTests(unittest.TestCase):
    def test_weyl_source_equation_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "cmb-weyl-source-equation-derived-as-linear-response-target")
        self.assertTrue(payload["weyl_source_equation_ready"])
        self.assertIn("Sigma_JH", payload["sigma_formula"])

    def test_transfer_integration_stays_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["weyl_transfer_function_integrated"])
        self.assertFalse(payload["proxy_replaced"])


if __name__ == "__main__":
    unittest.main()
