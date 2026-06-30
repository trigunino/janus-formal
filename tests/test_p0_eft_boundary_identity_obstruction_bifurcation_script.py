from __future__ import annotations

import unittest

from scripts.build_p0_eft_boundary_identity_obstruction_bifurcation import build_payload, render_markdown


class P0EFTBoundaryIdentityObstructionBifurcationTests(unittest.TestCase):
    def test_standard_sources_no_go_is_recorded(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["identity_obstruction_recorded"])
        self.assertTrue(status["standard_sources_no_go_if_qT_and_delta_nonzero"])
        self.assertFalse(status["pure_geometric_closure_available"])
        self.assertFalse(status["prediction_ready"])

    def test_eft_counterterm_closes_only_algebraically(self) -> None:
        payload = build_payload()
        status = payload["theorem_status"]

        self.assertTrue(status["eft_counterterm_closes_identity_channel"])
        self.assertFalse(status["eft_counterterm_source_derived_from_janus"])
        self.assertEqual(payload["eft_branch"]["exact_value"], "m_EFT = -4*q_T*Delta_chi")

    def test_obligations_force_choice(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("derive M_EFT", obligations)
        self.assertIn("final no-go", obligations)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("pure_geometric_closure_available: False", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
