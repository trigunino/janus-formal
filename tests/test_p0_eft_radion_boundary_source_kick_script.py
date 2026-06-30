from __future__ import annotations

import unittest

from scripts.build_p0_eft_radion_boundary_source_kick import build_payload, render_markdown


class P0EFTRadionBoundarySourceKickTests(unittest.TestCase):
    def test_source_is_boundary_variation_not_free_profile(self) -> None:
        payload = build_payload()
        status = payload["theorem_status"]

        self.assertTrue(status["source_defined_as_boundary_variation"])
        self.assertTrue(status["source_kick_structured"])
        self.assertIn("delta S_boundary", payload["source"]["definition"])

    def test_beta_response_branch_does_not_add_local_force(self) -> None:
        source = build_payload()["source"]

        self.assertIn("= 0", source["cartan_ghy_response"])
        self.assertIn("reopens", source["cartan_ghy_constant_beta_branch"])

    def test_no_fit_still_waits_for_bulk_potential(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["potential_V_fixed_from_Janus_action"])
        self.assertFalse(status["Omega_T_no_fit_ready"])

    def test_markdown_records_remaining_obligation(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("derive V(chi)", markdown)
        self.assertIn("source-kick-structured-potential-open", markdown)


if __name__ == "__main__":
    unittest.main()
