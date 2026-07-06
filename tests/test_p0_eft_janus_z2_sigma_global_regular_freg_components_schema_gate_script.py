import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_global_regular_freg_components_schema_gate import (
    build_payload,
)


class JanusZ2SigmaGlobalRegularFregComponentsSchemaGateTest(unittest.TestCase):
    def test_schema_and_template_define_strict_non_executable_input(self):
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
        self.assertIn("lambda_grid", schema["required"])
        self.assertIn("normal_frame_holonomy_defect", schema["required"])
        self.assertIn("collar_endpoint_mismatch", schema["required"])
        self.assertIn("junction_bianchi_defect", schema["required"])
        self.assertEqual(
            schema["properties"]["source"]["const"],
            "active_global_regularity_components",
        )
        self.assertIn("not an executable manifest", template)
        self.assertIn("lambda_grid = R_Sigma/ell_collar", template)


if __name__ == "__main__":
    unittest.main()
