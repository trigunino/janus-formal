import unittest

from scripts.build_p0_eft_janus_z4_regenerative_camb_z4_backend_gate import build_payload


class P0EFTJanusZ4RegenerativeCAMBZ4BackendGateTests(unittest.TestCase):
    def test_current_csv_backend_blocks_regenerative_gate(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-regenerative-camb-z4-backend-gate")
        self.assertEqual(payload["source_of_spectra"], "csv_fixed")
        self.assertFalse(payload["backend_regenerative"])
        self.assertFalse(payload["z4_deltas_regenerated_per_cosmology"])
        self.assertFalse(payload["no_stale_csv_reuse"])
        self.assertFalse(payload["local_cosmology_profiling_allowed"])
        self.assertFalse(payload["regenerative_gr_handshake_allowed"])
        self.assertFalse(payload["frozen_candidate_replay_allowed"])
        self.assertFalse(payload["full_planck_validation"])
        self.assertFalse(payload["gate_passed"])


if __name__ == "__main__":
    unittest.main()
