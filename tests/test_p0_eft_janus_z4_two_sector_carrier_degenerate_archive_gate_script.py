import unittest

from scripts.build_p0_eft_janus_z4_two_sector_carrier_degenerate_archive_gate import build_payload


class P0EFTJanusZ4TwoSectorCarrierDegenerateArchiveGateTests(unittest.TestCase):
    def test_archive_blocks_planck_and_preserves_history(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-two-sector-carrier-degenerate-archive-gate")
        self.assertTrue(payload["current_two_sector_source_archived"])
        self.assertEqual(payload["reason"], "carrier_A_s_tangent")
        self.assertGreaterEqual(payload["full_two_sector_parallel_fraction"], 0.8)
        self.assertEqual(payload["dominant_tangent_direction"], "A_s")
        self.assertTrue(payload["variables_gate_history_preserved"])
        self.assertTrue(payload["conservation_bianchi_history_preserved"])
        self.assertTrue(payload["initial_mode_history_preserved"])
        self.assertTrue(payload["linear_evolution_history_preserved"])
        self.assertTrue(payload["stability_history_preserved"])
        self.assertTrue(payload["source_level_history_preserved"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["retuning_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
