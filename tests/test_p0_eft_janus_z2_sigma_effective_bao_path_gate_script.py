import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts.build_p0_eft_janus_z2_sigma_effective_bao_path_gate import build_payload


class JanusZ2SigmaEffectiveBAOPathGateTest(unittest.TestCase):
    def test_missing_effective_closure_blocks_path(self):
        payload = build_payload()
        self.assertFalse(payload["effective_closure_ready"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertFalse(payload["scale_free_BAO_ready_from_two_parameters_alone"])

    def test_two_parameter_effective_closure_still_needs_bao_primitives(self):
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
            with patch(
                "scripts.build_p0_eft_janus_z2_sigma_effective_bao_path_gate.build_effective_closure_payload"
            ) as mocked:
                from scripts.build_p0_eft_janus_z2_sigma_effective_closure_input_gate import (
                    build_payload as build_closure,
                )

                mocked.return_value = build_closure(input_path=path)
                payload = build_payload()

        self.assertTrue(payload["effective_closure_ready"])
        self.assertTrue(payload["effective_observational_closure"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertFalse(payload["scale_free_BAO_ready_from_two_parameters_alone"])
        self.assertFalse(
            payload["required_after_effective_closure"]["background_E_Z2Sigma"][
                "can_be_derived_from_two_effective_parameters_alone"
            ]
        )


if __name__ == "__main__":
    unittest.main()

