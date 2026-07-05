import unittest

from scripts.build_p0_eft_janus_z2_sigma_bao_component_manifest_writer_gate import build_payload


class P0EFTJanusZ2SigmaBAOComponentManifestWriterGateTests(unittest.TestCase):
    def test_writer_gate_keeps_official_output_blocked_until_components_exist(self):
        payload = build_payload()

        self.assertTrue(payload["strict_component_manifest_writer_ready"])
        self.assertTrue(payload["writer_requires_all_active_component_functions"])
        self.assertTrue(payload["writer_requires_component_provenance"])
        self.assertTrue(payload["writer_rejects_forbidden_provenance_tokens"])
        self.assertTrue(payload["writer_produces_official_pipeline_compatible_schema"])
        self.assertFalse(payload["required_manifests_available"])
        self.assertFalse(payload["official_component_manifest_written"])
        self.assertFalse(payload["gate_passed"])


if __name__ == "__main__":
    unittest.main()
