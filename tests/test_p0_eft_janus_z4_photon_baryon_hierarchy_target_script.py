from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_photon_baryon_hierarchy_target import build_payload, write_reports


class P0EFTJanusZ4PhotonBaryonHierarchyTargetScriptTests(unittest.TestCase):
    def test_hierarchy_target_declares_standard_nonproxy_equations(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["hierarchy_target_ready"])
        self.assertFalse(payload["hierarchy_physical_ready"])
        self.assertIn("delta_gamma_prime", payload["equations"]["photon_continuity"])
        self.assertIn("theta_b_prime", payload["equations"]["baryon_euler"])
        self.assertFalse(payload["checks"]["coefficients_derived_from_action"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_photon_baryon_hierarchy_target.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_photon_baryon_hierarchy_target.md").exists())
        self.assertIn("tau_dot", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
