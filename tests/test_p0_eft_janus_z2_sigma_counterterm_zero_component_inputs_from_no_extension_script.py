import json
import tempfile
import unittest
from pathlib import Path

from scripts.write_p0_eft_janus_z2_sigma_counterterm_zero_component_inputs_from_no_extension import (
    build_payload,
)


class CountertermZeroComponentInputsFromNoExtensionTests(unittest.TestCase):
    def test_writes_zero_inputs_when_no_extension_audit_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            audit_path = root / "audit.json"
            grid_path = root / "grid.json"
            out_path = root / "counterterm_component_inputs.json"
            audit_path.write_text(
                json.dumps(
                    {
                        "remaining_non_GHY_channel_absence_proved": True,
                        "E_counterterm_zero_under_no_extension_policy": True,
                        "open_non_GHY_channels": {
                            "non_topological_cross_action_sigma_source": False
                        },
                        "cross_action_audit": {
                            "no_extension_policy_forbids_cross_action": True
                        },
                    }
                ),
                encoding="utf-8",
            )
            grid_path.write_text(json.dumps({"a_grid": [0.25, 0.5, 1.0]}), encoding="utf-8")

            payload = build_payload(
                audit_path=audit_path,
                grid_source_path=grid_path,
                output_path=out_path,
            )
            written = json.loads(out_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(written["counterterm_no_extension_zero_derived"])
        self.assertEqual(written["counterterm_rho"], [0.0, 0.0, 0.0])
        self.assertEqual(written["counterterm_p"], [0.0, 0.0, 0.0])
        self.assertFalse(written["fitted_counterterm_coefficient_used"])

    def test_blocks_when_audit_does_not_allow_zero(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            audit_path = root / "audit.json"
            grid_path = root / "grid.json"
            out_path = root / "counterterm_component_inputs.json"
            audit_path.write_text(
                json.dumps(
                    {
                        "remaining_non_GHY_channel_absence_proved": False,
                        "E_counterterm_zero_under_no_extension_policy": False,
                        "open_non_GHY_channels": {
                            "non_topological_cross_action_sigma_source": True
                        },
                        "cross_action_audit": {
                            "no_extension_policy_forbids_cross_action": False
                        },
                    }
                ),
                encoding="utf-8",
            )
            grid_path.write_text(json.dumps({"a_grid": [0.25, 0.5, 1.0]}), encoding="utf-8")

            payload = build_payload(
                audit_path=audit_path,
                grid_source_path=grid_path,
                output_path=out_path,
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(out_path.exists())


if __name__ == "__main__":
    unittest.main()
