import unittest

from scripts.build_p0_eft_janus_z4_master_no_retuning_replay_v2_gate import build_payload
from scripts.build_p0_eft_janus_z4_master_observed_planck_gr_reference_handshake_v2 import (
    write_reports as write_gr_handshake,
)
from scripts.build_p0_eft_janus_z4_master_observed_planck_wrapper_handshake_v2_gate import (
    write_reports as write_wrapper_handshake,
)
from scripts.build_p0_eft_janus_z4_master_official_likelihood_policy_v2_gate import (
    write_reports as write_policy,
)


class P0EFTJanusZ4MasterNoRetuningReplayV2GateTests(unittest.TestCase):
    def test_v2_replay_is_fixed_and_does_not_unlock_planck(self):
        write_policy()
        write_gr_handshake()
        write_wrapper_handshake()
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-no-retuning-replay-v2-gate")
        self.assertTrue(payload["observed_planck_wrapper_handshake_v2_gate_passed"])
        self.assertTrue(payload["normalization_fixed_to_a_sigma"])
        self.assertEqual(payload["selected_revision_fixed"], "shared_U_norm_silk_guard")
        self.assertTrue(payload["baseline_spectra_exists"])
        self.assertTrue(payload["candidate_spectra_exists"])
        self.assertTrue(payload["carrier_threshold_passed"])
        self.assertFalse(payload["lambda_retuning_allowed"])
        self.assertFalse(payload["normalization_retuning_allowed"])
        self.assertFalse(payload["revision_retuning_allowed"])
        self.assertFalse(payload["new_physics_channel_allowed"])
        self.assertTrue(payload["candidate_replayed_without_retuning"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
