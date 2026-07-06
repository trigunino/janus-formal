from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_null_sigma_variation_reduction_gate import build_payload


class Z2NullSigmaVariationReductionGateScriptTests(unittest.TestCase):
    def test_reduction_gate_keeps_null_junction_blocked(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["bulk_null_density_variation_reduced"])
        self.assertIn("PT joint", payload["next_required"][0])
        self.assertFalse(payload["null_junction_balance_ready"])


if __name__ == "__main__":
    unittest.main()
