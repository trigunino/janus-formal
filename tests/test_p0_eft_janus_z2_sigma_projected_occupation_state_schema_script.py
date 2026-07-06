import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_projected_occupation_state_schema import (
    build_payload,
)
from src.janus_lab.z2_sigma_projected_occupation_state import (
    validate_projected_occupation_state_payload,
)


class JanusZ2SigmaProjectedOccupationStateSchemaScriptTest(unittest.TestCase):
    def test_schema_and_template_are_written_without_active_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            schema_path = tmpdir / "schema.json"
            template_path = tmpdir / "template.md"
            example_path = tmpdir / "example.json"
            payload = build_payload(
                schema_path=schema_path,
                template_path=template_path,
                example_path=example_path,
            )
            schema = json.loads(schema_path.read_text(encoding="utf-8"))
            template = template_path.read_text(encoding="utf-8")
            example = json.loads(example_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["writes_active_manifest"])
        self.assertFalse(payload["example_is_active_manifest"])
        self.assertFalse(payload["template_is_executable_manifest"])
        self.assertIn("N_occ_Z2Sigma", schema["required"])
        self.assertEqual(schema["properties"]["source"]["const"], "explicit_state_initial_data")
        self.assertIn("not a no-fit theorem", template)
        self.assertIn("projected_occupation_state_inputs.json", template)
        self.assertEqual(example["N_occ_Z2Sigma"], 1.0)
        self.assertIn("not_active", example["N_occ_provenance"])

    def test_schema_template_shape_matches_validator(self):
        payload = validate_projected_occupation_state_payload(
            {
                "active_core": "Z2_tunnel_Sigma",
                "source": "explicit_state_initial_data",
                "full_no_fit_prediction_ready": False,
                "N_occ_Z2Sigma": 1.0,
                "N_occ_provenance": "declared_superselection_state_initial_data",
            }
        )

        self.assertEqual(payload["N_occ_Z2Sigma"], 1.0)


if __name__ == "__main__":
    unittest.main()
