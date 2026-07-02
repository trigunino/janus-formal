import unittest

from scripts.build_p0_eft_janus_z4_complete_gr_limit_shape_gate import build_payload


class P0EFTJanusZ4CompleteGRLimitShapeGateTests(unittest.TestCase):
    def test_gr_limit_gate_blocks_z4_planck_interpretation_when_shape_fails(self):
        payload = build_payload()

        self.assertFalse(payload["z4_enabled"])
        self.assertTrue(payload["native_gr_limit_solver_executed"])
        self.assertTrue(payload["camb_gr_reference_generated"])
        self.assertFalse(payload["observed_planck_validation"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["full_planck_validation"])
        if not payload["gr_limit_shape_passed"]:
            self.assertFalse(payload["z4_on_planck_interpretation_allowed"])
            self.assertEqual(payload["failure_interpretation"], "native_gr_limit_shape_mismatch")


if __name__ == "__main__":
    unittest.main()
