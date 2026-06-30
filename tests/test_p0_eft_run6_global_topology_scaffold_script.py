from __future__ import annotations

import unittest

from scripts.build_p0_eft_run6_global_topology_scaffold import build_payload, render_markdown


class P0EFTRun6GlobalTopologyScaffoldTests(unittest.TestCase):
    def test_run6_keeps_local_identities_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["local_closed"]["nieh_yan_eta_H_plus_2_residual"], "0")
        self.assertEqual(payload["local_closed"]["orbifold_3a_sigma_minus_2_residual"], "0")

    def test_global_theorems_remain_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run6_scaffold_ready"])
        self.assertTrue(status["numeric_solver_untouched"])
        self.assertFalse(status["aps_pin_global_theorem_proved"])
        self.assertFalse(status["orbifold_cover_global_theorem_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_two_global_interfaces(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("P0EFTAPSPinTraceNormalization", markdown)
        self.assertIn("P0EFTAPSPinTraceGlobalDerivation", markdown)
        self.assertIn("P0EFTOrbifoldVolumeCoverClassification", markdown)
        self.assertIn("P0EFTOrbifoldVolumeDerivation", markdown)


if __name__ == "__main__":
    unittest.main()
