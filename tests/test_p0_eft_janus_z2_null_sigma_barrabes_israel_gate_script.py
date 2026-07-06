from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_null_sigma_barrabes_israel_gate import build_payload


class Z2NullSigmaBarrabesIsraelGateScriptTests(unittest.TestCase):
    def test_barrabes_israel_gate_blocks_without_jump(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["transverse_curvature_plus_side"]["C_TT"], 0.5)
        self.assertTrue(payload["stress_slots"]["all_values_blocked_until_jump_C_ab"])
        self.assertIn("derive [C_ab]", payload["next_required"][1])


if __name__ == "__main__":
    unittest.main()
