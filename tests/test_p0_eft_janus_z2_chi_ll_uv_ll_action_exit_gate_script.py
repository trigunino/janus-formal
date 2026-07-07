import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_chi_ll_uv_ll_action_exit_gate import build_payload


class ChiLLUVLLActionExitGateTests(unittest.TestCase):
    def test_default_reaches_normalization_frontier(self):
        payload = build_payload(Path("missing-ll-normalization.json"))

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["UV_LL_action_exit_ready"])
        self.assertTrue(payload["structural_closure"]["chi_LL_composite_and_conserved"])
        self.assertTrue(payload["structural_closure"]["bridge_matching_available"])
        self.assertFalse(payload["structural_closure"]["normalization_manifest_valid"])

    def test_forbidden_shortcuts_are_explicit(self):
        shortcuts = build_payload(Path("missing-ll-normalization.json"))["forbidden_shortcuts"]

        self.assertTrue(shortcuts["choose_q_LL_by_fit"])
        self.assertTrue(shortcuts["choose_lambda_F2_by_fit"])
        self.assertTrue(shortcuts["reuse_auxiliary_sqrt_F2_units_as_SI_units"])

    def test_valid_normalization_manifest_closes_exit_conditionally(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "normalization.json"
            path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "branch": "Z2_null_Sigma_PT_bridge",
                        "source": "active_derived",
                        "L_F2_family": "monomial_lambda_F2_power_p",
                        "area_gauge": "physical_induced_S2_metric",
                        "normalization_proved": True,
                        "SO3_flux_ansatz_proved": True,
                        "flux_quantization_proved": True,
                        "normalization_provenance": "derived_uv_ll_action_unit_test",
                        "flux_integer_n": 1,
                        "q_LL_dimensionless": 2.0,
                        "lambda_F2": 3.0,
                        "power_p": 2.0,
                        "observational_fit_used": False,
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertTrue(payload["UV_LL_action_exit_ready"])
        self.assertTrue(payload["chi_LL_prediction_ready"])
        self.assertEqual(payload["blocked_by"], [])


if __name__ == "__main__":
    unittest.main()
