from __future__ import annotations

import unittest

from scripts.build_p0_route_c_geometric_exotic_completion_gate import build_payload, render_markdown


class P0RouteCGeometricExoticCompletionGateTests(unittest.TestCase):
    def test_ranks_geometric_routes_without_prediction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "geometric-exotic-routes-ranked-open")
        self.assertEqual(payload["preferred_order"][0], "BF_connection")
        self.assertEqual(payload["preferred_order"][1], "holonomy")
        self.assertTrue(payload["requires_same_l_for_k_qcross_vlasov"])
        self.assertFalse(payload["prediction_ready"])

    def test_candidates_include_expected_equations(self) -> None:
        text = " ".join(row["equations"] for row in build_payload()["candidates"])

        self.assertIn("F_Omega", text)
        self.assertIn("Omega=L^{-1}DL", text)
        self.assertIn("N_alpha", text)
        self.assertIn("phi_*mu_plus", text)
        self.assertIn("G_source", text)

    def test_markdown_reports_route_c(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Geometric Exotic", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
