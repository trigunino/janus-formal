from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_null_sigma_action_variation_gate import build_payload


class Z2NullSigmaActionVariationGateScriptTests(unittest.TestCase):
    def test_action_variation_gate_points_to_junction_work(self) -> None:
        payload = build_payload()

        self.assertIn("Lehner-Myers-Poisson-Sorkin", payload["bibliography"]["null_gr_action"])
        self.assertIn("derive delta(sqrt(q) kappa_l)", payload["next_required"][0])
        self.assertFalse(payload["null_junction_balance_ready"])


if __name__ == "__main__":
    unittest.main()
