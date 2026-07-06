from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_null_sigma_pt_joint_gate import build_payload


class Z2NullSigmaPTJointGateScriptTests(unittest.TestCase):
    def test_pt_joint_gate_does_not_close_junction(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["PT_joint_term_ready"])
        self.assertIn("Barrabes-Israel", payload["next_required"][0])
        self.assertFalse(payload["null_junction_balance_ready"])


if __name__ == "__main__":
    unittest.main()
