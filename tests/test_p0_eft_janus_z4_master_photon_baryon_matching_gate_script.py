import unittest

from scripts.build_p0_eft_janus_z4_master_photon_baryon_matching_gate import build_payload


class P0EFTJanusZ4MasterPhotonBaryonMatchingGateTests(unittest.TestCase):
    def test_matching_gate_blocks_after_acoustic_failure(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-photon-baryon-matching-gate")
        self.assertEqual(payload["input_failure_subclass"], "acoustic_phase_failure")
        self.assertFalse(payload["photon_baryon_matching_passed"])
        self.assertTrue(payload["source_mapping_requires_rederivation"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["planck_retry_allowed"])
        self.assertFalse(payload["new_physics_allowed"])
        self.assertFalse(payload["retuning_allowed"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
