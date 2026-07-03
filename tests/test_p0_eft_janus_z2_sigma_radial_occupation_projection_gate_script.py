import unittest

from scripts.build_p0_eft_janus_z2_sigma_radial_occupation_projection_gate import build_payload


class P0EFTJanusZ2SigmaRadialOccupationProjectionGateTests(unittest.TestCase):
    def test_radial_projection_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["radial_occupation_projection_ledger_declared"])
        self.assertTrue(payload["declared"]["rotation_equivariance_criterion_declared"])
        self.assertTrue(payload["declared"]["projected_radial_occupation_declared"])
        self.assertIn("equivariance", payload["formulas"])

    def test_radial_projection_closure_remains_blocked(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["projection_rotation_equivariant_derived"])
        self.assertFalse(payload["closure"]["projected_radial_occupation_derived"])
        self.assertFalse(payload["radial_occupation_projection_ready"])
        self.assertIn("feed_result_to_distribution_isotropy_anisotropic_stress_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
