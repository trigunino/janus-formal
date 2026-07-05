import unittest

from scripts.build_p0_eft_janus_z2_sigma_early_plasma_component_manifest_gate import build_payload


class P0EFTJanusZ2SigmaEarlyPlasmaComponentManifestGateTests(unittest.TestCase):
    def test_gate_declares_strict_early_plasma_manifest_contract(self):
        payload = build_payload()

        self.assertTrue(payload["writer_ready"])
        self.assertTrue(payload["loader_validation_ready"])
        self.assertTrue(payload["merge_into_bao_component_manifest_ready"])
        self.assertFalse(payload["manifest_exists"])
        self.assertFalse(payload["manifest_valid"])
        self.assertIn("Gamma_drag_Z2Sigma", payload["accepted_fields"])
        self.assertFalse(payload["early_plasma_values_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["requires_active_provenance"])
        self.assertTrue(payload["compressed_planck_lcdm_rd_forbidden"])
        self.assertTrue(payload["archived_z4_reuse_forbidden"])


if __name__ == "__main__":
    unittest.main()
