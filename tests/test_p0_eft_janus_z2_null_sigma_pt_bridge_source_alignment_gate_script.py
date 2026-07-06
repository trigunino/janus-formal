from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_null_sigma_pt_bridge_source_alignment_gate import (
    build_payload,
)


class Z2NullSigmaPTBridgeSourceAlignmentGateScriptTests(unittest.TestCase):
    def test_gate_blocks_regular_hk_and_points_to_null_variables(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["current_status"]["source_alignment_ready"])
        self.assertFalse(payload["hard_separation_from_regular_sigma"]["standard_GHY_Israel_Cartan_pipeline_allowed"])
        self.assertIn("declare null Sigma variables l,n,q_AB,theta,sigma_AB,kappa", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
