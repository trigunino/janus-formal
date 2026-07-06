from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_souriau_boundary_moment_map_alpha_route import (
    build_payload,
)


class SouriauBoundaryMomentMapAlphaRouteTests(unittest.TestCase):
    def test_souriau_route_is_not_counterterm_closure_without_boundary_hamiltonian(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["souriau_phase_space_route_available"])
        self.assertTrue(payload["boundary_moment_map_declared"])
        self.assertTrue(payload["moment_map_charge_conserved"])
        self.assertFalse(payload["sigma_hamiltonian_boundary_functional_available"])
        self.assertFalse(payload["moment_map_variation_to_alpha_h_available"])
        self.assertFalse(payload["moment_map_variation_to_alpha_K_available"])
        self.assertFalse(payload["closes_E_counterterm"])
        self.assertFalse(payload["closes_sigma_alpha_h"])
        self.assertEqual(
            payload["primary_blocker"],
            "missing_sigma_hamiltonian_boundary_functional",
        )

    def test_zero_rustine_guards(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["negative_energy_orientation_supported"])
        self.assertFalse(payload["negative_thermodynamic_density_postulated"])
        self.assertFalse(payload["observational_fit_used"])
        self.assertFalse(payload["archived_z4_reuse_used"])
        self.assertFalse(payload["free_surface_density_added"])


if __name__ == "__main__":
    unittest.main()
