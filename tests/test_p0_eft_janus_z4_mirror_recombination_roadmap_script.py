from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_mirror_recombination_roadmap import build_payload, write_reports


class P0EFTJanusZ4MirrorRecombinationRoadmapTests(unittest.TestCase):
    def test_roadmap_keeps_two_sectors_and_rejects_shortcuts(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-mirror-recombination-roadmap")
        self.assertTrue(payload["roadmap_only"])
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertIn("Phi_minus", payload["state_vector"])
        self.assertIn("Psi_plus", payload["state_vector"])
        self.assertFalse(payload["anti_shortcuts"]["collapse_to_rho_eff_before_projection_allowed"])
        self.assertFalse(payload["anti_shortcuts"]["fit_visibility_or_phase_by_observation_allowed"])
        self.assertTrue(payload["ready_to_implement_next_block"])

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_mirror_recombination_roadmap.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_mirror_recombination_roadmap.md").exists())


if __name__ == "__main__":
    unittest.main()
