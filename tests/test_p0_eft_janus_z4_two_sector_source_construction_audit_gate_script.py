import unittest

from scripts.build_p0_eft_janus_z4_two_sector_source_construction_audit_gate import build_payload


class P0EFTJanusZ4TwoSectorSourceConstructionAuditGateTests(unittest.TestCase):
    def test_audit_decomposes_sources_without_promotion(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-two-sector-source-construction-audit-gate")
        self.assertTrue(payload["full_source_archived"])
        rows = payload["component_projection_rows"]
        for name in (
            "plus_only_source",
            "minus_only_source",
            "symmetric_mode_source",
            "antisymmetric_Z4_mode_source",
            "relative_isocurvature_mode_source",
            "projection_only_source",
            "Weyl_source",
            "Theta0_source",
            "Pi_source",
        ):
            self.assertIn(name, rows)
            self.assertIn("parallel_fraction", rows[name])
            self.assertIn("dominant_tangent_direction", rows[name])
        self.assertIsInstance(payload["surviving_components_parallel_lt_0p7"], list)
        self.assertIsInstance(payload["any_component_survives"], bool)
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
