import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_effective_bao_parameter_schema_gate import (
    build_payload,
)


class JanusZ2SigmaEffectiveBAOParameterSchemaGateTest(unittest.TestCase):
    def test_schema_and_template_are_written_without_active_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            schema_path = tmpdir / "schema.json"
            template_path = tmpdir / "template.md"
            payload = build_payload(schema_path=schema_path, template_path=template_path)

            self.assertTrue(schema_path.exists())
            self.assertTrue(template_path.exists())
            schema = json.loads(schema_path.read_text(encoding="utf-8"))
            template = template_path.read_text(encoding="utf-8")

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["writes_active_manifest"])
        self.assertFalse(payload["template_is_executable_manifest"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertIn("effective_initial_data", schema["required"])
        self.assertIn("primitive_provenance", schema["required"])
        self.assertIn(
            "R_Sigma_over_ell_collar_Z2Sigma",
            schema["properties"]["effective_initial_data"]["required"],
        )
        self.assertNotIn(
            "R_Sigma_effective_Mpc",
            schema["properties"]["effective_initial_data"]["properties"],
        )
        self.assertEqual(
            schema["properties"]["source"]["const"],
            "effective_parameter_inputs",
        )
        self.assertIn("full_no_fit_prediction_ready = false", template)
        self.assertIn("Minimal JSON shape", template)
        self.assertIn("placeholders", template)


if __name__ == "__main__":
    unittest.main()
