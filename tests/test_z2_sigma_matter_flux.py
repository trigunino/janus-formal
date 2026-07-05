import unittest

import numpy as np

from janus_lab.z2_sigma_matter_flux import (
    build_active_matter_flux_projection_payload,
    build_bulk_stress_on_sigma_payload,
    build_transparent_matter_flux_component_payload,
    make_transparent_matter_flux_components,
    perfect_fluid_stress_covariant_grid,
    project_active_matter_flux_radial_values,
)


class Z2SigmaMatterFluxTests(unittest.TestCase):
    def test_transparent_matter_flux_builder_requires_active_transparency(self):
        with self.assertRaises(ValueError):
            make_transparent_matter_flux_components(active_sigma_transparency_derived=False)

    def test_transparent_matter_flux_builder_returns_zero_components(self):
        rho, pressure = make_transparent_matter_flux_components(active_sigma_transparency_derived=True)
        a = np.asarray([1.0, 0.5, 0.25])

        np.testing.assert_allclose(rho(a), np.zeros_like(a))
        np.testing.assert_allclose(pressure(a), np.zeros_like(a))

    def test_transparent_component_payload_rejects_forbidden_provenance(self):
        with self.assertRaises(ValueError):
            build_transparent_matter_flux_component_payload(
                a_grid=[0.25, 0.5, 1.0],
                active_sigma_transparency_derived=True,
                transparency_provenance="Planck LCDM prior",
            )

    def test_transparent_component_payload_contains_zero_arrays(self):
        payload = build_transparent_matter_flux_component_payload(
            a_grid=[0.25, 0.5, 1.0],
            active_sigma_transparency_derived=True,
            transparency_provenance="active Sigma transparency derivation",
        )

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["flrw_components_over_rho_crit0"]["matter_flux_rho"], [0.0, 0.0, 0.0])
        self.assertEqual(payload["flrw_components_over_rho_crit0"]["matter_flux_p"], [0.0, 0.0, 0.0])
        self.assertFalse(payload["archived_z4_reuse_used"])

    def test_active_projection_contracts_stress_tangents_normals(self):
        payload = project_active_matter_flux_radial_values(
            a_grid=[0.5, 1.0],
            T_plus_munu_values=[[[2.0, 3.0], [5.0, 7.0]], [[11.0, 13.0], [17.0, 19.0]]],
            T_minus_munu_values=[[[1.0, 2.0], [3.0, 4.0]], [[5.0, 6.0], [7.0, 8.0]]],
            tangent_vectors_values=[[[1.0, 0.0]], [[0.0, 1.0]]],
            normal_plus_values=[[0.0, 1.0], [1.0, 0.0]],
            normal_minus_values=[[1.0, 0.0], [0.0, 1.0]],
            radial_variation_tangent_weights=[[2.0], [3.0]],
            eps_Z2=-1.0,
        )

        self.assertEqual(payload["F_plus_tangent_values"], [[3.0], [17.0]])
        self.assertEqual(payload["F_minus_tangent_values"], [[1.0], [8.0]])
        self.assertEqual(payload["F_Z2Sigma_tangent_values"], [[2.0], [9.0]])
        self.assertEqual(payload["E_matterFlux_values"], [4.0, 27.0])

    def test_active_projection_payload_marks_strict_route(self):
        payload = build_active_matter_flux_projection_payload(
            {
                "a_grid": [0.5, 1.0],
                "T_plus_munu_values": [[[1.0, 0.0], [0.0, 1.0]], [[1.0, 0.0], [0.0, 1.0]]],
                "T_minus_munu_values": [[[0.0, 0.0], [0.0, 0.0]], [[0.0, 0.0], [0.0, 0.0]]],
                "tangent_vectors_values": [[[1.0, 0.0]], [[1.0, 0.0]]],
                "normal_plus_values": [[0.0, 1.0], [0.0, 1.0]],
                "normal_minus_values": [[0.0, 1.0], [0.0, 1.0]],
                "radial_variation_tangent_weights": [[1.0], [1.0]],
            }
        )

        self.assertTrue(payload["active_flux_projection_ready"])
        self.assertEqual(payload["selected_route"], "active_projection")
        self.assertFalse(payload["observational_H0_fit_used"])

    def test_perfect_fluid_stress_covariant_grid(self):
        stress = perfect_fluid_stress_covariant_grid(
            rho_values=[10.0],
            pressure_values=[2.0],
            metric_covariant_values=[[[-1.0, 0.0], [0.0, 3.0]]],
            four_velocity_contravariant_values=[[1.0, 0.0]],
        )

        self.assertEqual(stress, [[[10.0, 0.0], [0.0, 6.0]]])

    def test_bulk_stress_payload_builds_plus_minus_tensors(self):
        payload = build_bulk_stress_on_sigma_payload(
            {
                "a_grid": [0.5, 1.0],
                "rho_plus_values": [10.0, 20.0],
                "p_plus_values": [2.0, 4.0],
                "metric_plus_munu_values": [[[-1.0, 0.0], [0.0, 1.0]], [[-1.0, 0.0], [0.0, 1.0]]],
                "u_plus_contravariant_values": [[1.0, 0.0], [1.0, 0.0]],
                "rho_minus_values": [3.0, 5.0],
                "p_minus_values": [1.0, 2.0],
                "metric_minus_munu_values": [[[-1.0, 0.0], [0.0, 1.0]], [[-1.0, 0.0], [0.0, 1.0]]],
                "u_minus_contravariant_values": [[1.0, 0.0], [1.0, 0.0]],
            }
        )

        self.assertTrue(payload["bulk_stress_on_sigma_ready"])
        self.assertEqual(payload["T_plus_munu_values"][0], [[10.0, 0.0], [0.0, 2.0]])
        self.assertEqual(payload["T_minus_munu_values"][1], [[5.0, 0.0], [0.0, 2.0]])


if __name__ == "__main__":
    unittest.main()
