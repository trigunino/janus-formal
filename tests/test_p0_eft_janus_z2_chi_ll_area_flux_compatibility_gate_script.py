import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_chi_ll_area_flux_compatibility_gate import build_payload


class ChiLLAreaFluxCompatibilityGateTests(unittest.TestCase):
    def test_default_blocks_without_manifests(self):
        payload = build_payload(
            area_input_path=Path("missing-area.json"),
            flux_input_path=Path("missing-flux.json"),
        )

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["area_flux_compatibility_ready"])
        self.assertIn("area_gap_manifest_ready", payload["blocked_by"])
        self.assertIn("flux_superselection_manifest_ready", payload["blocked_by"])

    def test_compatible_area_and_flux_close_conditionally(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            area_path = base / "area.json"
            flux_path = base / "flux.json"
            area_path.write_text(
                json.dumps(
                    {
                        "quantum_area_operator_on_Sigma": True,
                        "A_gap_m2": 16.0 * math.pi,
                        "A_Sigma_equals_N_gap_A_gap_theorem": True,
                        "N_gap": 1,
                        "area_gauge": "physical_induced_S2_metric",
                        "non_observational_provenance": True,
                    }
                ),
                encoding="utf-8",
            )
            flux_path.write_text(
                json.dumps(
                    {
                        "active_core": "Z2_tunnel_Sigma",
                        "branch": "Z2_null_Sigma_PT_bridge",
                        "source": "active_derived",
                        "flux_cycle": "S2_throat",
                        "area_gauge": "physical_induced_S2_metric",
                        "F2_convention": "F_ab_F^ab_equals_2_B2_over_Rs4",
                        "SO3_flux_ansatz_proved": True,
                        "flux_quantization_proved": True,
                        "flux_integer_n": 4,
                        "q_LL_dimensionless": 1.0,
                        "F2_0_m_minus_4": 0.5,
                        "flux_state_provenance": "active_theory_unit_test",
                        "observational_fit_used": False,
                        "compressed_planck_lcdm_background_used": False,
                        "archived_z4_reuse_used": False,
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(area_input_path=area_path, flux_input_path=flux_path)

        self.assertTrue(payload["area_flux_compatibility_ready"])
        self.assertTrue(payload["chi_LL_prediction_ready"])
        self.assertAlmostEqual(payload["compatibility"]["area_R_s_m"], 2.0)
        self.assertAlmostEqual(payload["compatibility"]["flux_R_s_m"], 2.0)


if __name__ == "__main__":
    unittest.main()
