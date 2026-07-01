from __future__ import annotations

import unittest

from scripts.build_p0_eft_holst_stress_trace_derivation import build_payload


class P0EFTHolstStressTraceDerivationTests(unittest.TestCase):
    def test_trace_derivation_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "holst-stress-trace-derivation-run")
        self.assertTrue(payload["traceless_holst_stress_derived"])
        self.assertEqual(payload["coefficient_solution"]["c_pi"], "0")
        self.assertEqual(payload["coefficient_solution"]["c_q"], "1")
        self.assertEqual(payload["coefficient_solution"]["c_slip"], "1")

    def test_not_yet_camb_safe(self) -> None:
        self.assertFalse(build_payload()["cambridge_safe_to_patch"])


if __name__ == "__main__":
    unittest.main()
