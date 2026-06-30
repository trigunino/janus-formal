from __future__ import annotations

import unittest

from scripts.build_p0_route_d_no_go_structural_matrix import build_payload, render_markdown


class P0RouteDNoGoStructuralMatrixTests(unittest.TestCase):
    def test_matrix_excludes_easy_families_but_not_full_theorem(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "no-go-structural-matrix-open")
        self.assertEqual(payload["excluded_family_count"], 3)
        self.assertEqual(payload["open_family_count"], 2)
        self.assertTrue(payload["restricted_no_go_proved"])
        self.assertFalse(payload["full_no_go_proved"])
        self.assertFalse(payload["accepted_candidate_exists"])
        self.assertTrue(payload["free_tensor_routes_excluded"])
        self.assertTrue(payload["source_free_derivative_subfamily_excluded"])
        self.assertTrue(payload["source_derived_stf_operator_open"])
        self.assertTrue(payload["requires_janus_provenance"])
        self.assertTrue(payload["requires_ghost_stability"])
        self.assertFalse(payload["prediction_ready"])

    def test_matrix_keeps_tensor_and_curvature_open(self) -> None:
        rows = {row["family"]: row for row in build_payload()["matrix_rows"]}

        self.assertTrue(rows["pure_pullback"]["excluded"])
        self.assertTrue(rows["ultralocal_scalar"]["excluded"])
        self.assertTrue(rows["matter_scalar"]["excluded"])
        self.assertFalse(rows["tracefree_tensor"]["excluded"])
        self.assertFalse(rows["derivative_curvature"]["excluded"])

    def test_markdown_reports_structural_matrix(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("No-Go Structural Matrix", markdown)
        self.assertIn("Full no-go proved: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
