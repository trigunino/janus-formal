from __future__ import annotations

import unittest

from scripts.build_p0_eft_immirzi_geff_planck_gate import build_payload


class P0EFTImmirziGeffPlanckGateTests(unittest.TestCase):
    def test_naive_geff_gate_is_postfix_superseded(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "immirzi-geff-planck-gate-postfix-superseded")
        self.assertTrue(payload["pre_fix_static_result_invalidated"])
        self.assertFalse(payload["route_b_naive_geff_planck_accepted"])
        self.assertGreater(payload["postfix_gate"]["chi2_CMB"], 2000.0)


if __name__ == "__main__":
    unittest.main()
