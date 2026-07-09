import unittest

from scripts.build_p0_eft_janus_z4_two_sector_carrier_degenerate_closure_gate import build_payload


class P0EFTJanusZ4TwoSectorCarrierDegenerateClosureGateTests(unittest.TestCase):
    def test_closure_blocks_planck_and_preserves_trace(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-two-sector-carrier-degenerate-closure-gate")
        self.assertTrue(payload["current_two_sector_source_closed_as_carrier_degenerate"])
        self.assertEqual(payload["reason"], "carrier_A_s_tangent")
        self.assertGreaterEqual(payload["full_two_sector_parallel_fraction"], 0.8)
        self.assertEqual(payload["dominant_tangent_direction"], "A_s")
        self.assertTrue(payload["variables_gate_preserved"])
        self.assertTrue(payload["conservation_bianchi_gate_preserved"])
        self.assertTrue(payload["initial_mode_gate_preserved"])
        self.assertTrue(payload["linear_evolution_gate_preserved"])
        self.assertTrue(payload["stability_gate_preserved"])
        self.assertTrue(payload["source_level_regeneration_trace_preserved"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["retuning_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
