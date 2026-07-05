import unittest

from scripts.build_p0_eft_janus_z2_sigma_holst_nieh_yan_radial_block_gate import build_payload


class P0EFTJanusZ2SigmaHolstNiehYanRadialBlockGateTests(unittest.TestCase):
    def test_holst_nieh_yan_radial_block_is_structurally_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["holst_nieh_yan_radial_ledger_declared"])
        self.assertTrue(payload["holst_nieh_yan_radial_block_structurally_declared"])
        self.assertIn("NY_pullback", payload["structural_formula"])

    def test_holst_nieh_yan_of_a_waits_for_torsion_and_immirzi(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["Sigma_torsion_pullback_ready"])
        self.assertFalse(payload["closure"]["Immirzi_radial_profile_ready"])
        self.assertFalse(payload["holst_nieh_yan_radial_block_of_a_ready"])
        self.assertTrue(payload["declared"]["torsion_pullback_on_Sigma_gate_declared"])
        self.assertIn("pass_torsion_pullback_on_Sigma_gate", payload["next_required"])
        self.assertIn("derive_Sigma_torsion_pullback_from_active_Z2_Sigma_connection", payload["next_required"])

    def test_ready_torsion_and_immirzi_close_radial_block(self):
        payload = build_payload(
            torsion_pullback_payload={
                "status": "torsion",
                "torsion_pullback_on_sigma_ready": True,
                "closure": {"torsion_pullback_on_Sigma_ready": True},
                "current_frontier": [],
            },
            immirzi_profile_payload={
                "status": "immirzi",
                "immirzi_profile_of_a_ready": True,
                "primary_blocker": "none",
                "current_frontier": [],
            },
        )

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["holst_nieh_yan_radial_block_of_a_ready"])
        self.assertEqual(payload["primary_blocker"], "none")


if __name__ == "__main__":
    unittest.main()
