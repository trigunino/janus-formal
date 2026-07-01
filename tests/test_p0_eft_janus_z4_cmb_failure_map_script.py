from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_cmb_failure_map import build_payload, write_reports


class P0EFTJanusZ4CMBFailureMapTests(unittest.TestCase):
    def test_failure_map_tracks_obligations_without_claiming_planck(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-cmb-failure-map")
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertFalse(payload["official_planck_gate_passed"])
        locks = {item["lock"] for item in payload["failure_obligations"]}
        self.assertIn("TT_acoustic_source_phase_and_damping", locks)
        self.assertIn("low_l_SW_ISW_regularization", locks)
        self.assertIn("Weyl_lensing_projection_kernel", locks)
        self.assertIn("polarization_phase_and_visibility_guard", locks)
        self.assertTrue(payload["tt_swisw_derivation_ready"])
        self.assertFalse(payload["tt_swisw_branch_official_gate_passed"])
        self.assertIn("highl_TTTEEE", payload["tt_swisw_planck_delta_vs_integrated_gate"])
        self.assertTrue(payload["weyl_tt_transport_derivation_ready"])
        self.assertFalse(payload["weyl_tt_transport_branch_safe_for_gate"])

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_cmb_failure_map.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_cmb_failure_map.md").exists())


if __name__ == "__main__":
    unittest.main()
