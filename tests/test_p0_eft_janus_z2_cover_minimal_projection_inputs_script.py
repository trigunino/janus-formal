import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_cover_minimal_projection_inputs import build_payload


class JanusZ2CoverMinimalProjectionInputsScriptTest(unittest.TestCase):
    def test_writes_symbolic_projection_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            payload = build_payload(Path(tmp) / "projection.json")
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["writes_active_manifest"])
        self.assertFalse(payload["rho_eff_shortcut_used"])
        self.assertFalse(payload["observational_fit_used"])


if __name__ == "__main__":
    unittest.main()
