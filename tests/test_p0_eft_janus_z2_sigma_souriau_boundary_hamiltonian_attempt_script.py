from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_souriau_boundary_hamiltonian_attempt import (
    build_payload,
)


class SouriauBoundaryHamiltonianAttemptTests(unittest.TestCase):
    def test_global_charge_does_not_supply_local_alpha(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["moment_map_charge_Q_sigma_declared"])
        self.assertEqual(payload["deck_invariant_charge_reduction"], "Q_Sigma = N_occ")
        self.assertFalse(payload["absolute_occupation_fixed"])
        self.assertFalse(payload["mu_Sigma_available_from_existing_geometry"])
        self.assertFalse(payload["local_density_from_charge_available"])
        self.assertFalse(payload["metric_variation_available"])
        self.assertFalse(payload["extrinsic_curvature_variation_available"])
        self.assertFalse(payload["alpha_h_from_souriau_hamiltonian"])
        self.assertFalse(payload["alpha_K_from_souriau_hamiltonian"])
        self.assertFalse(payload["closes_E_counterterm"])
        self.assertEqual(
            payload["primary_blocker"],
            "moment_map_gives_global_charge_not_local_boundary_density",
        )

    def test_forbidden_shortcuts_are_explicit(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["not_a_rustine"])
        self.assertIn("set_mu_Sigma_by_observation", payload["forbidden_shortcuts"])
        self.assertIn(
            "identify_Q_Sigma_with_density_without_volume_or_state",
            payload["forbidden_shortcuts"],
        )
        self.assertIn(
            "differentiate_global_charge_as_if_it_were_local_surface_action",
            payload["forbidden_shortcuts"],
        )


if __name__ == "__main__":
    unittest.main()
