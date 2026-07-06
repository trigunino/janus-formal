import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_sigma_effective_partial_closure_from_projective_ratio import (
    build_payload,
)


class JanusZ2SigmaEffectivePartialClosureFromProjectiveRatioScriptTest(unittest.TestCase):
    def test_writes_derived_ratio_and_keeps_charge_open(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "partial.json"
            payload = build_payload(output_path=output)
            manifest = json.loads(output.read_text(encoding="utf-8"))

        self.assertTrue(payload["partial_effective_closure_ready"])
        self.assertFalse(payload["effective_closure_ready"])
        self.assertEqual(payload["R_Sigma_over_ell_collar_Z2Sigma"], 1.0)
        self.assertFalse(payload["projected_baryon_number_charge_Z2Sigma_ready"])
        self.assertEqual(
            payload["primary_blocker"],
            "superselection_state_or_initial_occupation_not_fixed",
        )
        self.assertEqual(
            manifest["derived_effective_initial_data"][
                "R_Sigma_over_ell_collar_Z2Sigma"
            ],
            1.0,
        )
        self.assertEqual(
            manifest["open_effective_initial_data"],
            ["projected_baryon_number_charge_Z2Sigma"],
        )


if __name__ == "__main__":
    unittest.main()
