from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_null_sigma_boundary_variables_gate import build_payload


class Z2NullSigmaBoundaryVariablesGateScriptTests(unittest.TestCase):
    def test_null_gate_declares_next_action_work(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["branch"], "Z2_null_Sigma_PT_bridge")
        self.assertTrue(payload["null_boundary_variables_declared"])
        self.assertFalse(payload["null_action_variation_ready"])


if __name__ == "__main__":
    unittest.main()
