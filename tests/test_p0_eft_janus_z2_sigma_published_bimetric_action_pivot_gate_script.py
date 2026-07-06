from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_published_bimetric_action_pivot_gate import (
    build_payload,
)


class PublishedBimetricActionPivotGateTests(unittest.TestCase):
    def test_pivot_changes_route_not_model(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["previous_starting_point_underselected"])
        self.assertEqual(
            payload["new_starting_point"],
            "published_bulk_bimetric_action_plus_bianchi_first",
        )
        self.assertFalse(payload["model_changed"])
        self.assertTrue(payload["route_changed"])
        self.assertTrue(payload["z2_tunnel_sigma_kept"])
        self.assertTrue(payload["z4_not_reopened"])
        self.assertFalse(payload["sigma_surface_action_extension_allowed"])
        self.assertTrue(payload["pivot_passed"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])

    def test_published_action_limitations_are_explicit(self) -> None:
        payload = build_payload()

        self.assertIn("determinant bridge factors", payload["published_action_supplies"])
        self.assertIn("Bianchi constraints on source slots", payload["published_action_supplies"])
        self.assertIn(
            "complete nonlinear interaction tensor",
            payload["published_action_does_not_supply"],
        )
        self.assertIn(
            "local Sigma counterterm density L_Sigma(h,K)",
            payload["published_action_does_not_supply"],
        )


if __name__ == "__main__":
    unittest.main()
