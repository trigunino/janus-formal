import unittest

from scripts.run_p0_eft_janus_z4_acoustic_phase_consistency_gate import (
    COMPONENT,
    REFINED_LAMBDAS,
    build_payload,
)


class P0EFTJanusZ4AcousticPhaseConsistencyGateTests(unittest.TestCase):
    def test_phase_gate_scaffold_without_official_likelihood(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "janus-z4-acoustic-phase-consistency-gate")
        self.assertEqual(payload["component"], COMPONENT)
        self.assertEqual(payload["trial_type"], "refined_effective_acoustic_temperature_source_delta")
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertFalse(payload["polarization_source_delta_enabled"])
        self.assertTrue(payload["EE_unchanged_by_construction"])
        self.assertTrue(payload["Cphiphi_unchanged_by_construction"])
        self.assertFalse(payload["recombination_delta_enabled"])
        self.assertFalse(payload["visibility_delta_enabled"])
        self.assertEqual(tuple(payload["lambda_grid"]), REFINED_LAMBDAS)
        self.assertFalse(payload["official_likelihood_requested"])
        self.assertFalse(payload["official_likelihood_executed"])
        self.assertFalse(payload["acoustic_phase_consistency_gate_passed"])
        for row in payload["diagnostics"].values():
            self.assertEqual(row["EE_max_delta"], 0.0)
            self.assertEqual(row["Cphiphi_max_delta"], 0.0)
            self.assertTrue(row["TE_sign_check"])


if __name__ == "__main__":
    unittest.main()
