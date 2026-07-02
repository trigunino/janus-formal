import unittest

from scripts.build_p0_eft_janus_z4_master_observed_planck_gr_reference_handshake_v2 import (
    write_reports as write_gr_handshake,
)
from scripts.build_p0_eft_janus_z4_master_observed_planck_wrapper_handshake_v2_gate import build_payload
from scripts.build_p0_eft_janus_z4_master_official_likelihood_policy_v2_gate import (
    write_reports as write_policy,
)


class P0EFTJanusZ4MasterObservedPlanckWrapperHandshakeV2GateTests(unittest.TestCase):
    def test_v2_observed_wrapper_gate_passes_gr_handshake_but_blocks_planck(self):
        write_policy()
        write_gr_handshake()
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-observed-planck-wrapper-handshake-v2-gate")
        self.assertTrue(payload["official_likelihood_policy_v2_declared"])
        self.assertFalse(payload["mock_wrappers_allowed"])
        self.assertFalse(payload["fallback_to_internal_pseudo_likelihood_allowed"])
        self.assertTrue(payload["observed_planck_wrapper_available"])
        self.assertTrue(payload["gr_reference_handshake_v2_report_present"])
        self.assertTrue(payload["gr_reference_handshake_on_same_wrapper_v2_passed"])
        self.assertTrue(payload["observed_planck_wrapper_handshake_v2_gate_passed"])
        self.assertFalse(payload["master_v2_no_retuning_replay"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["observational_claim_allowed"])


if __name__ == "__main__":
    unittest.main()
