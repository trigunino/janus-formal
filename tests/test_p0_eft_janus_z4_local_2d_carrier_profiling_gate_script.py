import unittest

from scripts.build_p0_eft_janus_z4_local_2d_carrier_profiling_gate import build_payload


class P0EFTJanusZ4Local2DCarrierProfilingGateTests(unittest.TestCase):
    def test_local_2d_carrier_profiles(self):
        payload = build_payload(run_official=True)

        self.assertEqual(payload["status"], "janus-z4-local-2d-carrier-profiling-gate")
        self.assertTrue(payload["lambda_frozen"])
        self.assertTrue(payload["no_lambda_retuning"])
        self.assertTrue(payload["no_new_physics"])
        self.assertTrue(payload["same_grid_for_GR_and_candidate"])
        self.assertTrue(payload["non_overlap_accounting_only"])
        self.assertFalse(payload["all_2d_pair_gains_survive"])
        self.assertFalse(payload["local_2d_carrier_profiled_effective_candidate"])
        for row in payload["pair_rows"].values():
            self.assertFalse(row["pair_gain_survives"])
            self.assertGreater(
                row["summaries"]["combined_highl"]["candidate_gain_after_2d_carrier_profile"],
                0.0,
            )
            self.assertGreater(
                row["summaries"]["decomposed_highl"]["candidate_gain_after_2d_carrier_profile"],
                0.0,
            )
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
