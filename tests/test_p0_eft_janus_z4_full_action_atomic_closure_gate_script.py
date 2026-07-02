import unittest

from scripts.build_p0_eft_janus_z4_full_action_atomic_closure_gate import build_payload


class P0EFTJanusZ4FullActionAtomicClosureGateTests(unittest.TestCase):
    def test_action_closure_reduced_but_not_closed(self):
        payload = build_payload()

        self.assertTrue(payload["atomic_action_obligations"]["linearized_action_ready"])
        self.assertTrue(payload["atomic_action_obligations"]["determinant_measure_physical_ready"])
        self.assertTrue(payload["atomic_action_obligations"]["assembly_scaffold_ready"])
        self.assertFalse(payload["unique_action_variation_closed"])
        self.assertNotIn("determinant_measure_physical_ready", payload["remaining_action_obligations"])
        self.assertIn("full_boundary_action_closed", payload["remaining_action_obligations"])
        self.assertIn("ward_closure_ready", payload["remaining_action_obligations"])
        self.assertEqual(
            payload["refined_boundary_gate"],
            "p0_eft_janus_z4_nonlinear_boundary_variation_obligation_gate",
        )
        self.assertEqual(
            payload["refined_ward_gate"],
            "p0_eft_janus_z4_ward_atomic_closure_gate",
        )
        self.assertEqual(
            payload["refined_el_residual_gate"],
            "p0_eft_janus_z4_nonlinear_el_residual_obligation_gate",
        )
        self.assertEqual(
            payload["refined_gauge_gate"],
            "p0_eft_janus_z4_gauge_fixing_variation_uniqueness_gate",
        )
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
