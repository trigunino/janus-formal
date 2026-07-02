import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_master_unlensed_lensed_split_gate import build_payload as split_payload
from scripts.build_p0_eft_janus_z4_master_lensing_remap_policy_gate import build_payload as policy_payload
from scripts.build_p0_eft_janus_z4_master_solver_implementation_readiness_gate import build_payload as solver_payload
from scripts.build_p0_eft_janus_z4_master_future_observed_planck_diagnostic_readiness_gate import build_payload as future_payload


class P0EFTJanusZ4MasterObservationalReadinessChainTests(unittest.TestCase):
    def test_split_and_future_observed_gate_without_validation(self):
        split = split_payload()
        policy = policy_payload()
        solver = solver_payload()
        future = future_payload()

        self.assertTrue(split["unlensed_lensed_split_available"])
        self.assertTrue(Path(split["unlensed_spectra_path"]).exists())
        self.assertTrue(Path(split["lensed_spectra_path"]).exists())
        self.assertTrue(policy["policy_allows_future_observed_diagnostic"])
        self.assertTrue(solver["solver_implemented"])
        self.assertTrue(solver["unlensed_lensed_split_available"])
        self.assertTrue(future["future_observed_planck_diagnostic_allowed"])
        self.assertFalse(future["observed_planck_validation"])
        self.assertFalse(future["candidate_promotion_allowed"])
        self.assertFalse(future["retuning_allowed"])
        self.assertFalse(future["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
