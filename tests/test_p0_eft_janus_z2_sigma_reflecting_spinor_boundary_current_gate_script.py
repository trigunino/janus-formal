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

    def test_normal_current_zero_waits_for_active_projection(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["spinor_boundary_projection_map_ready"])
        self.assertTrue(payload["closure"]["Z2_normal_orientation_ready"])
        self.assertTrue(payload["closure"]["local_MIT_current_zero_algebra_ready"])
        self.assertFalse(payload["closure"]["reflecting_boundary_condition_derived"])
        self.assertFalse(payload["closure"]["boundary_leakage_zero_derived"])
        self.assertFalse(payload["normal_dirac_current_zero_ready"])
        self.assertIn(
            "derive_reflecting_boundary_condition_without_free_phase",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
