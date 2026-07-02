import unittest

from scripts.build_p0_eft_janus_z4_master_observed_planck_gr_reference_handshake_v2 import build_payload


class P0EFTJanusZ4MasterObservedPlanckGRReferenceHandshakeV2Tests(unittest.TestCase):
    def test_v2_gr_reference_handshake_checks_same_wrapper_without_candidate_replay(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-observed-planck-gr-reference-handshake-v2")
        self.assertTrue(payload["all_observed_wrappers_available"])
        self.assertTrue(payload["Cl_vs_Dl_convention_checked"])
        self.assertTrue(payload["units_checked"])
        self.assertTrue(payload["TE_sign_checked"])
        self.assertTrue(payload["ell_indexing_checked"])
        self.assertTrue(payload["nuisance_vector_checked"])
        self.assertTrue(payload["foreground_handling_checked"])
        self.assertTrue(payload["GR_reference_sanity_checked"])
        self.assertTrue(payload["gr_reference_handshake_v2_passed"])
        self.assertFalse(payload["candidate_z4_replay_performed"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["observational_claim_allowed"])


if __name__ == "__main__":
    unittest.main()
