import unittest

from scripts.build_p0_eft_janus_z2_sigma_bao_component_manifest_schema_gate import build_payload


class P0EFTJanusZ2SigmaBAOComponentManifestSchemaGateTests(unittest.TestCase):
    def test_component_manifest_schema_declares_required_active_fields(self):
        payload = build_payload()

        self.assertTrue(payload["schema_declared"])
        self.assertTrue(payload["template_is_documentation_only"])
        self.assertIn("flrw_components_over_rho_crit0", payload["required_fields"])
        self.assertIn("early_plasma", payload["required_fields"])
        self.assertIn("critical_normalization", payload["required_fields"])
        self.assertIn("scalar_provenance", payload["required_fields"])
        self.assertIn("component_provenance", payload["required_fields"])
        self.assertIn("z_d_bracket", payload["optional_fields"])
        self.assertIn("cartan_ghy_rho", payload["flrw_component_fields"])
        self.assertIn("Gamma_drag_Z2Sigma", payload["early_plasma_fields"])
        self.assertIn("kappa_rho_crit0_Z2Sigma_SI", payload["critical_normalization_fields"])
        self.assertIn("H0_Z2Sigma", payload["scalar_provenance_fields"])
        self.assertTrue(payload["component_provenance_required"])

    def test_component_manifest_schema_forbids_bad_provenance(self):
        payload = build_payload()

        self.assertEqual(payload["required_provenance"]["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["required_provenance"]["source"], "active_derived")
        self.assertFalse(payload["required_provenance"]["compressed_planck_lcdm_rd_used"])
        self.assertFalse(payload["required_provenance"]["archived_z4_reuse_used"])
        self.assertFalse(payload["required_provenance"]["phenomenological_holst_bao_scan_used"])


if __name__ == "__main__":
    unittest.main()
