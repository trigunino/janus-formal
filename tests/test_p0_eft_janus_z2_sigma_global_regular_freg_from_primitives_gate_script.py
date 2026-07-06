import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_global_regular_freg_from_primitives_gate import (
    build_payload,
)
from tests.test_z2_sigma_global_regularity_primitives import _payload


class JanusZ2SigmaGlobalRegularFregFromPrimitivesGateTest(unittest.TestCase):
    def test_missing_primitives_blocks(self):
        payload = build_payload(input_path=Path("__missing_freg_primitives__.json"))
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["component_manifest_written"])
        self.assertEqual(payload["primary_blocker"], "global_regular_freg_primitives_json")

    def test_writes_components_and_selects_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmpdir = Path(tmp)
            primitive = tmpdir / "global_regular_freg_primitives.json"
            component = tmpdir / "global_regular_freg_components.json"
            primitive.write_text(json.dumps(_payload()), encoding="utf-8")
            payload = build_payload(input_path=primitive, component_output_path=component)
            written = json.loads(component.read_text(encoding="utf-8"))
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["component_manifest_written"])
        self.assertEqual(payload["regularity_roots"], [2.0])
        self.assertEqual(written["source"], "active_global_regularity_components")
        self.assertFalse(written["full_no_fit_prediction_ready"])


if __name__ == "__main__":
    unittest.main()
