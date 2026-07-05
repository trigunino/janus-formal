import unittest

from scripts.build_p0_eft_janus_z2_sigma_bao_active_readiness_gate import build_payload


class P0EFTJanusZ2SigmaBAOActiveReadinessGateTests(unittest.TestCase):
    def test_desi_data_are_available_but_active_bao_is_not_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["bibliography_checked"])
        self.assertEqual(payload["data_points"], 13)
        self.assertEqual(payload["covariance_shape"], [13, 13])
        self.assertTrue(payload["data_inputs"]["desi_dr2_gaussian_bao_mean_ready"])
        self.assertTrue(payload["data_inputs"]["desi_dr2_gaussian_bao_covariance_ready"])
        self.assertFalse(payload["active_input_status"]["manifest_exists"])
        self.assertFalse(payload["active_input_status"]["manifest_valid"])
        self.assertTrue(payload["calculator"]["strict_H_Z2Sigma_builder_ready"])
        self.assertTrue(payload["calculator"]["strict_effective_fluid_assembler_ready"])
        self.assertTrue(payload["calculator"]["effective_fluid_assembler_requires_active_FLRW_components"])
        self.assertTrue(payload["calculator"]["H_builder_requires_active_H0_Z2Sigma"])
        self.assertTrue(payload["calculator"]["H_builder_requires_active_rho_eff_over_rho_crit0"])
        self.assertTrue(payload["calculator"]["strict_c_s_Z2Sigma_builder_ready"])
        self.assertTrue(payload["calculator"]["c_s_builder_requires_active_baryon_density"])
        self.assertTrue(payload["calculator"]["c_s_builder_requires_active_photon_density"])
        self.assertTrue(payload["calculator"]["strict_z_d_Z2Sigma_solver_ready"])
        self.assertTrue(payload["calculator"]["z_d_solver_requires_active_H_Z2Sigma"])
        self.assertTrue(payload["calculator"]["z_d_solver_requires_active_drag_rate"])
        self.assertTrue(payload["calculator"]["strict_z2_sigma_bao_calculator_ready"])
        self.assertTrue(payload["calculator"]["strict_z2_sigma_sound_ruler_integrator_ready"])
        self.assertTrue(payload["calculator"]["calculator_requires_active_H_Z2Sigma"])
        self.assertTrue(payload["calculator"]["calculator_requires_active_rd_Z2Sigma"])
        self.assertTrue(payload["calculator"]["sound_ruler_integrator_requires_active_c_s_Z2Sigma"])
        self.assertTrue(payload["calculator"]["sound_ruler_integrator_requires_active_z_d_Z2Sigma"])
        self.assertTrue(payload["calculator"]["calculator_has_no_planck_lcdm_defaults"])
        self.assertFalse(payload["bao_prediction_vector_ready"])
        self.assertFalse(payload["bao_chi2_evaluated"])

    def test_active_inputs_and_forbidden_reuse_are_explicit(self):
        payload = build_payload()

        self.assertFalse(payload["active_inputs"]["H_Z2Sigma_numerical_ready"])
        self.assertFalse(payload["active_inputs"]["c_s_Z2Sigma_ready"])
        self.assertFalse(payload["active_inputs"]["z_d_Z2Sigma_ready"])
        self.assertFalse(payload["active_inputs"]["r_d_Z2Sigma_evaluated"])
        self.assertTrue(payload["forbidden_reuse"]["compressed_planck_lcdm_rd_forbidden"])
        self.assertTrue(payload["forbidden_reuse"]["planck_like_scale_forbidden"])
        self.assertTrue(payload["forbidden_reuse"]["archived_z4_bao_reuse_forbidden"])
        self.assertFalse(payload["nonfit_materialization"]["uses_compressed_planck_lcdm"])
        self.assertFalse(payload["nonfit_materialization"]["uses_archived_z4"])
        self.assertFalse(payload["nonfit_materialization"]["passed"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
