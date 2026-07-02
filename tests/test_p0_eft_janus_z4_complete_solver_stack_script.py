import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_complete_likelihood_ready_theory_vector_gate import build_payload


class P0EFTJanusZ4CompleteSolverStackTests(unittest.TestCase):
    def test_complete_solver_stack_exports_theory_vector_without_validation(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-complete-likelihood-ready-theory-vector-gate")
        self.assertTrue(payload["likelihood_ready_theory_vector_available"])
        self.assertTrue(payload["per_cosmology_regeneration_passed"])
        self.assertTrue(payload["contains_lensed_tt_te_ee"])
        self.assertTrue(payload["contains_cl_phiphi"])
        self.assertTrue(Path(payload["theory_vector_path"]).exists())
        self.assertTrue(payload["observed_likelihood_diagnostic_allowed"])
        self.assertFalse(payload["observed_planck_validation"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
