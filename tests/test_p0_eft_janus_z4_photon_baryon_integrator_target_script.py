from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_photon_baryon_integrator_target import build_payload, write_reports


class P0EFTJanusZ4PhotonBaryonIntegratorTargetScriptTests(unittest.TestCase):
    def test_integrator_target_produces_finite_stable_trajectory(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["finite_trajectory_produced"])
        self.assertTrue(payload["single_sector_limit_stable"])
        self.assertTrue(payload["z4_metric_sources_inserted"])
        self.assertTrue(payload["thomson_drag_inserted"])
        self.assertLess(payload["max_abs_state"], 1.0e-2)
        self.assertFalse(payload["calibrated_boltzmann_integrator_executed"])
        self.assertFalse(payload["photon_baryon_hierarchy_nonproxy"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_photon_baryon_integrator_target.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_photon_baryon_integrator_target.md").exists())
        self.assertIn("Boltzmann hierarchy", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
