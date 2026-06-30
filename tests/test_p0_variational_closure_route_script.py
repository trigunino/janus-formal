from __future__ import annotations

import unittest

from scripts.build_p0_variational_closure_route import build_payload


class P0VariationalClosureRouteTests(unittest.TestCase):
    def test_route_is_open_and_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["route"], "variational-action-closure")
        self.assertEqual(payload["status"], "open-not-derived")
        self.assertFalse(payload["action_supplied"])
        self.assertFalse(payload["euler_lagrange_identities_supplied"])
        self.assertFalse(payload["noether_bianchi_identity_supplied"])
        self.assertFalse(payload["stress_energy_variation_supplied"])
        self.assertFalse(payload["symmetry_constraints_supplied"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_required_identities_cover_variational_closure(self) -> None:
        items = {row["item"] for row in build_payload()["required_identities"]}

        self.assertIn("Interaction action", items)
        self.assertIn("Euler-Lagrange closure", items)
        self.assertIn("Diffeomorphism Noether identity", items)
        self.assertIn("Stress-energy variation", items)
        self.assertIn("Symmetry constraints", items)

    def test_no_fitted_potential_shortcut(self) -> None:
        payload = build_payload()
        gate = " ".join(payload["acceptance_gate"])

        self.assertFalse(payload["allows_fitted_potentials"])
        self.assertIn("no fitted potentials", gate)
        self.assertIn("not a separate optical fit", gate)

    def test_links_same_action_to_f_equals_d_l(self) -> None:
        relation = build_payload()["source_derived_relation"]

        self.assertIn("F = D L", relation["required"])
        self.assertIn("source-derived", relation["required"])
        self.assertIn("tune K or Q_cross independently", relation["not_allowed"])
        self.assertEqual(relation["status"], "open")


if __name__ == "__main__":
    unittest.main()
