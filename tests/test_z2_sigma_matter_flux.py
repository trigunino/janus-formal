import unittest

import numpy as np

from janus_lab.z2_sigma_matter_flux import (
    build_transparent_matter_flux_component_payload,
    make_transparent_matter_flux_components,
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


if __name__ == "__main__":
    unittest.main()
