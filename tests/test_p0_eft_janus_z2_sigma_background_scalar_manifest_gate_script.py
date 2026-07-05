import unittest

from scripts.build_p0_eft_janus_z2_sigma_background_scalar_manifest_gate import build_payload


class P0EFTJanusZ2SigmaBackgroundScalarManifestGateTests(unittest.TestCase):
    def test_gate_declares_strict_background_scalar_manifest_contract(self):
        payload = build_payload()

        self.assertTrue(payload["writer_ready"])
        self.assertTrue(payload["loader_validation_ready"])
        self.assertFalse(payload["manifest_exists"])
        self.assertFalse(payload["manifest_valid"])
        self.assertIn("H0_Z2Sigma_km_s_Mpc", payload["accepted_fields"])
        self.assertIn("critical_normalization", payload["accepted_fields"])
        self.assertTrue(payload["requires_active_provenance"])
        self.assertFalse(payload["background_scalar_values_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["compressed_planck_lcdm_background_forbidden"])
        self.assertTrue(payload["archived_z4_background_reuse_forbidden"])


if __name__ == "__main__":
    unittest.main()
