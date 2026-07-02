import csv
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_complete_observed_nonoverlap_accounting_gate import build_payload as accounting_payload
from scripts.build_p0_eft_janus_z4_complete_observed_planck_diagnostic_gate import build_payload as diagnostic_payload
from scripts.build_p0_eft_janus_z4_complete_observed_planck_diagnostic_gate import write_reports as diagnostic_reports


class P0EFTJanusZ4CompleteObservedPlanckDiagnosticTests(unittest.TestCase):
    def test_complete_solver_exports_planck_ready_csv_but_does_not_validate_by_default(self):
        payload = diagnostic_payload(run_observed=False)
        candidate_path = Path(payload["candidate_spectra_path"])

        self.assertTrue(candidate_path.exists())
        self.assertGreaterEqual(payload["ell_max"], 2508)
        with candidate_path.open(newline="", encoding="utf-8") as handle:
            header = next(csv.DictReader(handle)).keys()
        self.assertEqual(set(header), {"ell", "cl_tt", "cl_te", "cl_ee", "cl_pp"})
        self.assertFalse(payload["run_observed_executed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["full_planck_validation"])

    def test_nonoverlap_accounting_stays_blocked_without_observed_run(self):
        diagnostic_reports(run_observed=False)
        payload = accounting_payload()

        self.assertFalse(payload["observed_trial_executed"])
        self.assertTrue(payload["legacy_overlapping_total_diagnostic_only"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
