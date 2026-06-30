from __future__ import annotations

import unittest

from scripts.build_p0_route_c_phi_r_curvature_identity_gate import build_payload, render_markdown


class P0RouteCPhiRCurvatureIdentityGateTests(unittest.TestCase):
    def test_identity_blocks_free_phi_r_without_claiming_closure(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "phi-r-curvature-identity-gate-open")
        self.assertFalse(payload["free_phi_r_allowed"])
        self.assertTrue(payload["curvature_identity_available"])
        self.assertFalse(payload["curvature_identity_sufficient"])
        self.assertFalse(payload["phi_l_source_derived"])
        self.assertFalse(payload["path_rule_source_derived"])
        self.assertFalse(payload["same_l_transport_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_identity_rows_cover_connection_curvature_transport_holonomy(self) -> None:
        objects = {row["object"] for row in build_payload()["identity_rows"]}

        self.assertEqual(objects, {"relative_connection", "relative_curvature", "transport", "holonomy"})

    def test_markdown_forbids_shortcuts(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Free Phi_R allowed: False", markdown)
        self.assertIn("Q_det or Q_cross", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
