import unittest

from scripts.build_p0_eft_janus_z2_sigma_bao_manifest_schema_gate import build_payload


class P0EFTJanusZ2SigmaBAOManifestSchemaGateTests(unittest.TestCase):
    def test_manifest_schema_is_declared_with_forbidden_provenance(self):
        payload = build_payload()

        self.assertTrue(payload["schema_declared"])
        self.assertTrue(payload["writer_ready"])
        self.assertTrue(payload["loader_validation_ready"])
        self.assertIn("omega_k_Z2Sigma", payload["required_fields"])
        self.assertEqual(payload["required_provenance"]["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["required_provenance"]["source"], "active_derived")
        self.assertFalse(payload["required_provenance"]["compressed_planck_lcdm_rd_used"])
        self.assertFalse(payload["required_provenance"]["archived_z4_reuse_used"])
        self.assertFalse(payload["required_provenance"]["phenomenological_holst_bao_scan_used"])
        self.assertTrue(payload["official_chi2_requires_manifest"])


if __name__ == "__main__":
    unittest.main()
