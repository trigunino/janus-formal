import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_sigma_effective_bao_constant_primitive_diagnostic import (
    build_payload,
)
from src.janus_lab.z2_sigma_effective_bao import (
    load_effective_scale_free_primitive_inputs,
)


class JanusZ2SigmaEffectiveBAOConstantPrimitiveDiagnosticScriptTest(unittest.TestCase):
    def test_writes_valid_diagnostic_primitive_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            closure = Path(tmp) / "closure.json"
            output = Path(tmp) / "primitive.json"
            closure.write_text("{}", encoding="utf-8")
            payload = build_payload(closure_path=closure, output_path=output)
            manifest = json.loads(output.read_text(encoding="utf-8"))
            loaded = load_effective_scale_free_primitive_inputs(output)

        self.assertTrue(payload["diagnostic_primitives_written"])
        self.assertFalse(payload["writes_active_manifest"])
        self.assertFalse(payload["primitive_values_are_physical_derivation"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertEqual(manifest["source"], "effective_primitives")
        self.assertGreater(loaded.z_max, 1000.0)


if __name__ == "__main__":
    unittest.main()
