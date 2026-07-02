import unittest

from scripts.build_p0_eft_janus_z4_projection_parity_preservation_gate import build_payload


class P0EFTJanusZ4ProjectionParityPreservationGateTests(unittest.TestCase):
    def test_projection_parity_gate_blocks_observational_use(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-projection-parity-preservation-gate")
        rows = payload["projection_rows"]
        for name in (
            "value_projection",
            "normal_derivative_projection",
            "jump_projection",
            "membrane_weighted_projection",
            "mixed_value_derivative_projection",
        ):
            self.assertIn(name, rows)
            self.assertIn("antisymmetric_survival_ratio", rows[name])
            self.assertIn("projected_antisymmetric_parallel_fraction", rows[name])
            self.assertIn("preserves_antisymmetry", rows[name])
        self.assertIsInstance(payload["which_projection_preserves_antisymmetry"], list)
        self.assertFalse(payload["free_projection_coefficient_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
