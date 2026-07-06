from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_null_sigma_branch_verdict_gate import build_payload


class Z2NullSigmaBranchVerdictGateScriptTests(unittest.TestCase):
    def test_verdict_points_to_regular_pt_transfer_route(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["verdict"]["null_branch_exhausted_without_sparadrap"])
        self.assertEqual(
            payload["verdict"]["recommended_next_active_route"],
            "chapter_6_7_regular_PT_transfer_cross_term_surface",
        )
        self.assertIn("derive h_ab and K_ab", payload["next_required"][1])


if __name__ == "__main__":
    unittest.main()
