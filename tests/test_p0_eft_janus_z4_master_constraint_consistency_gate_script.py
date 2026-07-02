import unittest

from scripts.build_p0_eft_janus_z4_master_constraint_consistency_gate import build_payload


class P0EFTJanusZ4MasterConstraintConsistencyGateTests(unittest.TestCase):
    def test_constraints_are_declared_but_blocked(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-constraint-consistency-gate")
        self.assertTrue(payload["master_reconstruction_gate_passed"])
        self.assertTrue(payload["constraint_checks_declared"])
        self.assertFalse(payload["all_constraints_passed"])
        for status in payload["constraint_checks"].values():
            self.assertEqual(status, "blocked_until_master_reconstruction")
        self.assertTrue(payload["Bianchi_consistency_required"])
        self.assertTrue(payload["Pi_from_multipoles_required"])
        self.assertFalse(payload["independent_downstream_source_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])


if __name__ == "__main__":
    unittest.main()
