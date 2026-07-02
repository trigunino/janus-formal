import unittest

from scripts.build_p0_eft_janus_z4_minus_sector_decoupling_law_gate import build_payload


class P0EFTJanusZ4MinusSectorDecouplingLawGateTests(unittest.TestCase):
    def test_decoupling_law_gate_blocks_without_microphysics(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-minus-sector-decoupling-law-gate")
        self.assertTrue(payload["thermal_ratio_gate_completed"])
        self.assertFalse(payload["minus_decoupling_law_declared"])
        self.assertTrue(payload["minus_recombination_solver_required"])
        self.assertFalse(payload["free_decoupling_shift_allowed"])
        self.assertFalse(payload["free_visibility_patch_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
