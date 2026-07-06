import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_effective_closure_input_gate import (
    build_payload,
)


class JanusZ2SigmaEffectiveClosureInputGateTest(unittest.TestCase):
    def test_missing_input_blocks_gate(self):
        payload = build_payload(
            input_path=Path("__missing_effective_closure__.json"),
            partial_path=Path("__missing_partial__.json"),
            occupation_path=Path("__missing_occupation__.json"),
        )
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertEqual(payload["primary_blocker"], "effective_closure_inputs_json")

    def test_partial_ratio_without_occupation_reports_precise_blocker(self):
        with tempfile.TemporaryDirectory() as tmp:
            partial = Path(tmp) / "partial.json"
            partial.write_text("{}", encoding="utf-8")
            payload = build_payload(
                input_path=Path(tmp) / "missing_effective.json",
                partial_path=partial,
                occupation_path=Path(tmp) / "missing_occupation.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["partial_projective_ratio_exists"])
        self.assertFalse(payload["projected_occupation_state_input_exists"])
        self.assertEqual(payload["primary_blocker"], "projected_occupation_state_inputs_json")
        self.assertIn(
            "write outputs/active_z2_sigma/projected_occupation_state_inputs.json",
            payload["next_required"],
        )

    def test_valid_input_passes_as_effective_not_no_fit(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "effective_closure_inputs.json"
            path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "source": "effective_initial_data",
                        "compressed_planck_lcdm_used": False,
                        "archived_z4_reuse_used": False,
                        "observational_fit_used": False,
                        "full_no_fit_prediction_ready": False,
                        "effective_initial_data": {
                            "R_Sigma_over_ell_collar_Z2Sigma": 1.0,
                            "projected_baryon_number_charge_Z2Sigma": 2.0,
                        },
                        "effective_initial_data_provenance": {
                            "R_Sigma_over_ell_collar_Z2Sigma": "declared_effective_initial_data",
                            "projected_baryon_number_charge_Z2Sigma": "declared_effective_initial_data",
                        },
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path=path)
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["effective_closure_ready"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])


if __name__ == "__main__":
    unittest.main()

