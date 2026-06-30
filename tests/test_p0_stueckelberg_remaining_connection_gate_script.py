from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_remaining_connection_gate import build_payload, render_markdown


class P0StueckelbergRemainingConnectionGateTests(unittest.TestCase):
    def test_gate_localizes_remaining_connection_residual(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "remaining-connection-gate-open")
        self.assertTrue(payload["all_density_terms_reduced"])
        self.assertTrue(payload["dlogb_absorbed_conditionally"])
        self.assertTrue(payload["dl_terms_localized"])
        self.assertFalse(payload["connection_residual_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_remaining_terms_are_both_sector_connection_contractions(self) -> None:
        terms = " ".join(row["term"] for row in build_payload()["remaining"])

        self.assertIn("C_plus-minus", terms)
        self.assertIn("C_minus-plus", terms)
        self.assertIn("u_-to+", terms)
        self.assertIn("u_+to-", terms)

    def test_possible_closures_include_three_routes(self) -> None:
        routes = {row["route"] for row in build_payload()["possible_closures"]}

        self.assertIn("receiver_geodesic_transport", routes)
        self.assertIn("map_eom_force_balance", routes)
        self.assertIn("special_geometry", routes)

    def test_markdown_keeps_no_fit_acceptance(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("no observational boundary tuning", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
