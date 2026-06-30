from __future__ import annotations

import unittest

from scripts.build_p0_pulled_particle_action_cuu_derivation import build_payload, render_markdown


class P0PulledParticleActionCuuDerivationTests(unittest.TestCase):
    def test_particle_variation_gives_connection_force_skeleton(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "pulled-particle-action-cuu-derivation-partial")
        self.assertTrue(payload["geodesic_residual_zero"])
        self.assertTrue(payload["particle_geodesic_variation_closed"])
        self.assertTrue(payload["cold_dust_lift_closed"])
        self.assertTrue(payload["conditional_e_alpha_rho_cuu_supported"])
        self.assertFalse(payload["full_e_alpha_rho_cuu_derived"])

    def test_cross_pullback_algebra_closes_but_same_phi_l_remains_open(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["connection_difference_identity_status"],
            "connection-difference-cuu-identity-closed-algebraic",
        )
        self.assertTrue(payload["connection_difference_cross_pullback_closed"])
        self.assertFalse(payload["same_phi_l_source_selected"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_derivation_rows_name_closed_and_open_parts(self) -> None:
        rows = {row["row"]: row for row in build_payload()["derivation_rows"]}

        self.assertTrue(rows["particle_action_variation"]["closed"])
        self.assertTrue(rows["connection_rewrite"]["closed"])
        self.assertTrue(rows["dust_lift"]["closed"])
        self.assertTrue(rows["cross_pullback"]["closed"])
        self.assertFalse(rows["same_phi_l_selection"]["closed"])

    def test_markdown_keeps_no_full_claim(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Geodesic residual zero: True", markdown)
        self.assertIn("Connection-difference cross pullback closed: True", markdown)
        self.assertIn("Full E_alpha=rho Cuu derived: False", markdown)


if __name__ == "__main__":
    unittest.main()
