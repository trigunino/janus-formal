from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_cmb_diagnostic_master_report import build_payload, write_reports


class P0EFTJanusZ4CMBDiagnosticMasterReportScriptTests(unittest.TestCase):
    def test_master_report_audits_diagnostics_and_verdict(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-cmb-diagnostic-master-report")
        self.assertTrue(payload["all_diagnostic_requirements_met"])
        self.assertFalse(payload["official_planck_gate_passed"])
        self.assertTrue(payload["physical_closure_triad_ready"])
        self.assertTrue(payload["action_upstream_transport_ready"])
        self.assertFalse(payload["planck_validation_claimed_by_upstream_transport"])
        self.assertTrue(payload["requirements"]["legacy_cmb_not_required_for_active_validation"])
        self.assertTrue(payload["requirements"]["physical_closure_audits_scaffolded"])
        self.assertTrue(payload["requirements"]["action_upstream_transport_ready"])
        self.assertTrue(payload["algebraic_closure_flags"]["polarization_algebraic_closure_verified"])
        self.assertTrue(payload["algebraic_closure_flags"]["scalar_conditional_partial_closure_verified"])
        self.assertTrue(payload["algebraic_closure_flags"]["lensing_algebraic_projection_verified"])
        self.assertTrue(payload["physical_closure_flags"]["polarization_hierarchy_physical_ready"])
        self.assertTrue(payload["physical_closure_flags"]["scalar_swisw_physical_ready"])
        self.assertTrue(payload["physical_closure_flags"]["lensing_projection_physical_ready"])
        self.assertIn("highl_TE_observational_shape_after_polarization_transport", {item["lock"] for item in payload["remaining_locks"]})
        self.assertIn("low_l_TT_observational_SW_ISW_after_scalar_transport", {item["lock"] for item in payload["remaining_locks"]})

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_cmb_diagnostic_master_report.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_cmb_diagnostic_master_report.md").exists())
        self.assertTrue(payload["requirements"]["official_planck_available_gates_rerun"])


if __name__ == "__main__":
    unittest.main()
