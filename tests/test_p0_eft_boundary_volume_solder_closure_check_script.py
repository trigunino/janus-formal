from __future__ import annotations

import unittest

from scripts.build_p0_eft_boundary_volume_solder_closure_check import build_payload, render_markdown


class P0EFTBoundaryVolumeSolderClosureCheckTests(unittest.TestCase):
    def test_formal_solution_exists_but_is_not_geometric_yet(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["volume_solder_source_tested"])
        self.assertTrue(status["identity_channel_can_be_cancelled"])
        self.assertTrue(status["full_linear_system_has_formal_solution"])
        self.assertFalse(status["lambda_derived_from_janus_geometry"])
        self.assertFalse(status["pure_geometric_closure_proved"])
        self.assertFalse(status["prediction_ready"])

    def test_solution_contains_expected_values(self) -> None:
        solution = build_payload()["solution"]

        self.assertEqual(solution["lambda_exact"], "-4*q_T")
        self.assertIn("2*q_A", solution["kappa_exact"])
        self.assertIn("Delta_chi", solution["beta_exact"])

    def test_volume_source_targets_identity_only(self) -> None:
        source = build_payload()["source"]

        self.assertEqual(source["channel"], "identity only")
        self.assertIn("log(det(E_plus)/det(E_minus))", source["candidate"])

    def test_markdown_keeps_ready_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("formal-solution-found-geometric-normalization-open", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
