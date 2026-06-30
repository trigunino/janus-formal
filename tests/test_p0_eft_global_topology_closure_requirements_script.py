from __future__ import annotations

import unittest

from scripts.build_p0_eft_global_topology_closure_requirements import build_payload, render_markdown


class P0EFTGlobalTopologyClosureRequirementsTests(unittest.TestCase):
    def test_local_identities_are_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["local_identities"]["eta_H_plus_2_residual"], "0")
        self.assertEqual(payload["local_identities"]["three_a_sigma_minus_2_residual"], "0")

    def test_global_requirements_block_no_fit(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run6_aps_pin_interface_scaffolded"])
        self.assertTrue(status["run6_orbifold_cover_interface_scaffolded"])
        self.assertTrue(status["run8_orbifold_volume_derivation_scaffolded"])
        self.assertFalse(status["aps_global_normalization_closed"])
        self.assertFalse(status["orbifold_global_cover_closed"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_aps_and_orbifold(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("APS/Pin-", markdown)
        self.assertIn("Vol_+:Vol_-=2:1", markdown)


if __name__ == "__main__":
    unittest.main()
