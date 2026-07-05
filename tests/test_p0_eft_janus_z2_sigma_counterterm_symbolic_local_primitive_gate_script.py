import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_counterterm_symbolic_local_primitive_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCountertermSymbolicLocalPrimitiveGateTests(unittest.TestCase):
    def test_writes_symbolic_primitive_without_radial_profile(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "primitive.json"
            payload = build_payload(output_path=output)

            self.assertTrue(payload["symbolic_local_primitive_ready"])
            self.assertTrue(payload["symbolic_local_primitive_written"])
            self.assertTrue(output.exists())
            written = json.loads(output.read_text(encoding="utf-8"))
            self.assertEqual(written["counterterm_primitive_kind"], "symbolic_local_field_space_primitive")
            self.assertIn("R_K", written["residual_one_form"])
            self.assertFalse(written["coefficient_expansion_explicit"])
            self.assertFalse(written["radial_profile_ready"])
            self.assertFalse(written["fitted_counterterm_coefficient_used"])

    def test_radial_followup_is_still_required(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["closure"]["coefficient_expansion_explicit"])
        self.assertFalse(payload["closure"]["radial_profile_ready"])
        self.assertIn(
            "run_counterterm_lct_radial_profile_from_residual_contractions",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
