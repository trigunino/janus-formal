import tempfile
import unittest
from pathlib import Path

import numpy as np

import scripts.build_p0_eft_janus_z2_sigma_effective_fluid_closure_gate as effective_gate
import scripts.build_p0_eft_janus_z2_sigma_numerical_background_closure_gate as gate
from janus_lab.z2_sigma_background_manifest import write_active_z2sigma_background_scalar_manifest
from janus_lab.z2_sigma_flrw_component_manifest import write_active_z2sigma_flrw_component_manifest


class P0EFTJanusZ2SigmaNumericalBackgroundClosureGateTests(unittest.TestCase):
    def test_structural_background_is_not_yet_numeric_background(self):
        payload = gate.build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["prerequisites"]["background_equations_derived"])
        self.assertTrue(payload["prerequisites"]["effective_fluid_structural_projection_ready"])
        self.assertFalse(payload["prerequisites"]["effective_fluid_numeric_closure_ready"])
        self.assertFalse(payload["prerequisites"]["active_tunnel_embedding_of_a_closure_ready"])
        self.assertFalse(payload["prerequisites"]["rho_eff_Z2Sigma_of_a_ready"])
        self.assertFalse(payload["prerequisites"]["p_eff_Z2Sigma_of_a_ready"])
        self.assertTrue(payload["prerequisites"]["H_Z2Sigma_callable_builder_ready"])
        self.assertTrue(payload["prerequisites"]["E_Z2Sigma_dimensionless_callable_builder_ready"])
        self.assertFalse(payload["prerequisites"]["active_H0_Z2Sigma_ready"])
        self.assertFalse(payload["prerequisites"]["active_omega_k_Z2Sigma_ready"])
        self.assertFalse(payload["prerequisites"]["active_G_Z2Sigma_ready"])
        self.assertFalse(payload["upstream_frontiers"]["background_scalar_manifest"]["exists"])
        self.assertFalse(payload["upstream_frontiers"]["background_scalar_manifest"]["valid"])
        self.assertFalse(payload["numerical_background_prerequisites_ready"])
        self.assertTrue(payload["H_Z2Sigma_callable_builder_ready"])
        self.assertTrue(payload["E_Z2Sigma_dimensionless_callable_builder_ready"])
        self.assertFalse(payload["numerical_H_Z2Sigma_ready"])
        self.assertFalse(payload["numerical_E_Z2Sigma_ready"])
        self.assertFalse(payload["numerical_Omega_m_Z2Sigma_ready"])
        self.assertFalse(
            payload["upstream_frontiers"]["effective_fluid"]["effective_fluid_numeric_closure_ready"]
        )
        self.assertFalse(
            payload["upstream_frontiers"]["active_embedding"]["active_embedding_readiness_ready"]
        )

    def test_no_lcdm_or_z4_background_reuse(self):
        payload = gate.build_payload()

        self.assertTrue(payload["prerequisites"]["observational_parameter_fit_forbidden"])
        self.assertTrue(payload["prerequisites"]["legacy_lcdm_background_reuse_forbidden"])
        self.assertTrue(payload["prerequisites"]["archived_z4_background_reuse_forbidden"])
        self.assertIn("X_plus_Z2Sigma(a)", payload["missing_functions"])
        self.assertIn("close_active_tunnel_embedding_of_a_gate", payload["next_required"])
        self.assertIn("feed_active_H0_omega_k_and_rho_eff_into_existing_H_builder", payload["next_required"])

    def test_strict_background_and_flrw_manifests_enable_h_callable_readiness(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            background_path = tmpdir / "background_scalars.json"
            flrw_path = tmpdir / "flrw_components.json"
            write_active_z2sigma_background_scalar_manifest(
                background_path,
                h0_z2sigma_km_s_mpc=70.0,
                omega_k_z2sigma=0.0,
                gravitational_constant_si_z2sigma=6.67430e-11,
                scalar_provenance={
                    "H0_Z2Sigma": "active_background_scale",
                    "omega_k_Z2Sigma": "active_projective_curvature",
                    "G_Z2Sigma": "active_low_energy_gravity_convention",
                },
            )
            a = np.asarray([0.5, 1.0])
            zeros = [0.0, 0.0]
            write_active_z2sigma_flrw_component_manifest(
                flrw_path,
                a_grid=a,
                flrw_components_over_rho_crit0={
                    "cartan_ghy_rho": [1.0, 0.5],
                    "cartan_ghy_p": zeros,
                    "holst_nieh_yan_rho": zeros,
                    "holst_nieh_yan_p": zeros,
                    "matter_flux_rho": zeros,
                    "matter_flux_p": zeros,
                    "counterterm_rho": zeros,
                    "counterterm_p": zeros,
                },
                component_provenance={
                    "cartan_ghy_rho": "active_cartan",
                    "cartan_ghy_p": "active_cartan",
                    "holst_nieh_yan_rho": "active_holst",
                    "holst_nieh_yan_p": "active_holst",
                    "matter_flux_rho": "active_flux",
                    "matter_flux_p": "active_flux",
                    "counterterm_rho": "active_counterterm",
                    "counterterm_p": "active_counterterm",
                },
            )
            old_background = gate.BACKGROUND_SCALAR_MANIFEST_PATH
            old_flrw = effective_gate.FLRW_COMPONENT_MANIFEST_PATH
            gate.BACKGROUND_SCALAR_MANIFEST_PATH = background_path
            effective_gate.FLRW_COMPONENT_MANIFEST_PATH = flrw_path
            try:
                payload = gate.build_payload()
            finally:
                gate.BACKGROUND_SCALAR_MANIFEST_PATH = old_background
                effective_gate.FLRW_COMPONENT_MANIFEST_PATH = old_flrw

        self.assertTrue(payload["prerequisites"]["active_H0_Z2Sigma_ready"])
        self.assertTrue(payload["prerequisites"]["active_omega_k_Z2Sigma_ready"])
        self.assertTrue(payload["prerequisites"]["active_G_Z2Sigma_ready"])
        self.assertTrue(payload["prerequisites"]["rho_eff_Z2Sigma_of_a_ready"])
        self.assertTrue(payload["prerequisites"]["p_eff_Z2Sigma_of_a_ready"])
        self.assertTrue(payload["numerical_H_Z2Sigma_ready"])
        self.assertTrue(payload["numerical_E_Z2Sigma_ready"])
        self.assertFalse(payload["numerical_background_prerequisites_ready"])


if __name__ == "__main__":
    unittest.main()
