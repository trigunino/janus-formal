from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_transverse_source_requirement import build_payload


class P0TransverseSourceRequirementTests(unittest.TestCase):
    def test_best_route_is_projected_map_variation(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertEqual(decision["best_no_new_field_route"], "projected phi/L Euler-Lagrange source")
        self.assertTrue(decision["external_multiplier_rejected"])
        self.assertFalse(decision["source_derived"])
        self.assertFalse(decision["prediction_ready"])

    def test_required_identity_targets_projected_connection_residual(self) -> None:
        payload = build_payload()
        target = payload["required_identity"]["target"]

        self.assertIn("h^mu_nu", target)
        self.assertIn("C^nu_{alpha beta}", target)
        self.assertEqual(payload["required_identity"]["status"], "required-not-proved")

    def test_external_transverse_multiplier_is_not_existing(self) -> None:
        payload = build_payload()
        external = [row for row in payload["candidate_sources"] if row["name"] == "external_transverse_multiplier"][0]

        self.assertFalse(external["can_be_existing"])
        self.assertIn("reject", external["obligation"])


if __name__ == "__main__":
    unittest.main()
