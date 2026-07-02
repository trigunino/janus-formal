import unittest

from scripts.build_p0_eft_janus_z4_full_derived_slip_carrier_archive_gate import build_payload


class P0EFTJanusZ4FullDerivedSlipCarrierArchiveGateTests(unittest.TestCase):
    def test_full_derived_slip_is_archived_as_carrier_tangent(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-full-derived-slip-carrier-archive-gate")
        self.assertGreaterEqual(payload["full_derived_slip_parallel_fraction"], 0.85)
        self.assertEqual(payload["dominant_tangent_direction"], "A_s")
        self.assertTrue(payload["full_derived_slip_carrier_tangent"])
        self.assertTrue(payload["archive_fast"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertTrue(payload["no_lambda_retuning"])
        self.assertTrue(payload["no_free_slip_parameter"])
        self.assertTrue(payload["no_free_eta_ratio"])
        self.assertTrue(payload["no_direct_Cl_patch"])
        self.assertTrue(payload["raw_toy_LOS_forbidden"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
