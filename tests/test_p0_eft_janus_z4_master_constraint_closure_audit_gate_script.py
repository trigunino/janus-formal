import unittest

from scripts.build_p0_eft_janus_z4_master_constraint_closure_audit_gate import build_payload


class P0EFTJanusZ4MasterConstraintClosureAuditGateTests(unittest.TestCase):
    def test_master_source_constraints_close_without_observational_unlock(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-constraint-closure-audit-gate")
        self.assertTrue(payload["master_source_level_regeneration_gate_passed"])
        self.assertTrue(payload["all_constraint_closure_checks_passed"])
        self.assertLessEqual(payload["max_constraint_residual"], payload["closure_tolerance"])
        self.assertTrue(payload["Doppler_continuity_consistency_closed"])
        self.assertTrue(payload["Pi_from_multipoles_consistency_closed"])
        self.assertTrue(payload["trace_free_slip_consistency_closed"])
        self.assertTrue(payload["all_sources_use_same_U_Z4"])
        self.assertFalse(payload["independent_downstream_source_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])


if __name__ == "__main__":
    unittest.main()
