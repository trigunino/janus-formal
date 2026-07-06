import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_normal_connection_frame_primitives_schema_gate import (
    build_payload,
)


class NormalConnectionFramePrimitivesSchemaGateScriptTest(unittest.TestCase):
    def test_writes_schema_and_template_without_active_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(
                schema_path=Path(tmp) / "schema.json",
                template_path=Path(tmp) / "template.md",
            )
        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["writes_active_manifest"])
        self.assertFalse(payload["template_is_executable_manifest"])


if __name__ == "__main__":
    unittest.main()
