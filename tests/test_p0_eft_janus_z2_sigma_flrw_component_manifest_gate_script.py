import unittest
import tempfile
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_flrw_component_manifest_gate import build_payload


class Z2SigmaFLRWComponentManifestGateScriptTests(unittest.TestCase):
    def test_gate_reports_writer_and_merge_ready_without_values(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(manifest_path=Path(tmp) / "missing.json")

        self.assertTrue(payload["writer_ready"])
        self.assertTrue(payload["loader_validation_ready"])
        self.assertTrue(payload["merge_into_bao_component_manifest_ready"])
        self.assertFalse(payload["manifest_exists"])
        self.assertFalse(payload["manifest_valid"])
        self.assertFalse(payload["flrw_component_values_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["archived_z4_reuse_forbidden"])


if __name__ == "__main__":
    unittest.main()
