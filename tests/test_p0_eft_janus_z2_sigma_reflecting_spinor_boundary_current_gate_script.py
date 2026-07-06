import unittest

from scripts.build_p0_eft_janus_z2_sigma_reflecting_spinor_boundary_current_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaReflectingSpinorBoundaryCurrentGateTests(unittest.TestCase):
    def test_reflecting_boundary_current_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["reflecting_spinor_boundary_current_ledger_declared"])
        self.assertTrue(payload["declared"]["MIT_bag_boundary_current_bibliography_checked"])
        self.assertIn("J_n", payload["formulas"]["reflecting_current_condition"])
        self.assertTrue(payload["source_links"])

    def test_local_reflecting_condition_is_derived_but_global_projection_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["spinor_boundary_projection_map_ready"])
        self.assertTrue(payload["closure"]["Z2_normal_orientation_ready"])
        self.assertTrue(payload["closure"]["local_MIT_current_zero_algebra_ready"])
        self.assertTrue(payload["closure"]["local_reflecting_boundary_condition_derived"])
        self.assertTrue(payload["closure"]["local_boundary_leakage_zero_derived"])
        self.assertTrue(payload["closure"]["reflecting_boundary_condition_derived"])
        self.assertTrue(payload["closure"]["boundary_leakage_zero_derived"])
        self.assertTrue(payload["local_normal_dirac_current_zero_ready"])
        self.assertFalse(payload["normal_dirac_current_zero_ready"])
        self.assertEqual(payload["primary_blocker"], "spinor_boundary_projection_map_ready")
        self.assertIn("derive_global_Z2Sigma_spinor_projection_map", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
