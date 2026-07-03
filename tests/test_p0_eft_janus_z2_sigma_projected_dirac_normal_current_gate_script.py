import unittest

from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_normal_current_gate import build_payload


class P0EFTJanusZ2SigmaProjectedDiracNormalCurrentGateTests(unittest.TestCase):
    def test_projected_dirac_normal_current_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["projected_dirac_normal_current_ledger_declared"])
        self.assertTrue(payload["declared"]["projected_Dirac_matter_current_gate_declared"])
        self.assertTrue(payload["declared"]["Z2_projected_normal_current_declared"])

    def test_normal_current_waits_for_current_and_normals(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["projected_Dirac_matter_current_ready"])
        self.assertFalse(payload["closure"]["Sigma_normals_ready"])
        self.assertFalse(payload["no_normal_dirac_current_ready"])
        self.assertIn("derive_or_reject_J_n_Z2Sigma_equals_zero", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
