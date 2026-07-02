import unittest

from scripts.build_p0_eft_janus_z4_volume_solder_counterterm_bridge_gate import build_payload


class P0EFTJanusZ4VolumeSolderCountertermBridgeGateTests(unittest.TestCase):
    def test_volume_solder_derives_identity_counterterm_but_not_full_boundary(self):
        payload = build_payload()

        self.assertTrue(payload["volume_solder_identity_source_closed"])
        self.assertTrue(payload["counterterm_derived_from_janus_invariant"])
        self.assertTrue(payload["eft_identity_branch_closes_algebraically"])
        self.assertFalse(payload["pure_boundary_closure_available"])
        self.assertFalse(payload["full_boundary_action_closed"])
        self.assertEqual(
            payload["remaining_boundary_obligation"],
            "close_nonlinear_boundary_variation",
        )
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
