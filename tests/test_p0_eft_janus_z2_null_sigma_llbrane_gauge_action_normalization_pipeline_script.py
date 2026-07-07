import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_null_sigma_llbrane_gauge_action_normalization_pipeline import (
    build_payload,
)


def valid_input() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "source": "active_derived",
        "L_F2_family": "monomial_lambda_F2_power_p",
        "area_gauge": "physical_induced_S2_metric",
        "normalization_proved": True,
        "SO3_flux_ansatz_proved": True,
        "flux_quantization_proved": True,
        "flux_integer_n": 2,
        "q_LL_dimensionless": 0.5,
        "lambda_F2": 0.25,
        "power_p": 1.0,
        "normalization_provenance": "active_ll_gauge_sector_derivation",
        "observational_fit_used": False,
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
    }


class LLBraneGaugeActionNormalizationPipelineTests(unittest.TestCase):
    def test_missing_input_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            payload = build_payload(
                input_path=base / "missing.json",
                action_output_path=base / "action.json",
                flux_output_path=base / "flux.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["downstream_chi_reducer_ready"])

    def test_forbidden_provenance_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            input_path = base / "normalization.json"
            data = valid_input()
            data["normalization_provenance"] = "bao fit"
            input_path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(
                input_path=input_path,
                action_output_path=base / "action.json",
                flux_output_path=base / "flux.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn(
            "normalization_provenance_missing_or_forbidden",
            payload["validation_errors"],
        )

    def test_valid_input_writes_action_and_flux_manifests(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            input_path = base / "normalization.json"
            action_path = base / "action.json"
            flux_path = base / "flux.json"
            input_path.write_text(json.dumps(valid_input()), encoding="utf-8")
            payload = build_payload(
                input_path=input_path,
                action_output_path=action_path,
                flux_output_path=flux_path,
                write_output=True,
            )
            self.assertTrue(action_path.exists())
            self.assertTrue(flux_path.exists())
            action_payload = json.loads(action_path.read_text(encoding="utf-8"))
            flux_payload = json.loads(flux_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["F2_0_m_minus_4"], 0.5)
        self.assertEqual(action_payload["F2_units"], "m_minus_4")
        self.assertEqual(flux_payload["F2_0_m_minus_4"], 0.5)


if __name__ == "__main__":
    unittest.main()
