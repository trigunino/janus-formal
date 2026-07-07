import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_null_sigma_chi_ll_superselection_flux_reducer_gate import (
    build_payload,
)
from scripts.build_p0_eft_janus_z2_null_sigma_mass_charge_to_rs_gate import C_SI, G_SI


def valid_input() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "branch": "Z2_null_Sigma_PT_bridge",
        "source": "active_derived",
        "flux_cycle": "S2_throat",
        "area_gauge": "physical_induced_S2_metric",
        "F2_convention": "F_ab_F^ab_equals_2_B2_over_Rs4",
        "SO3_flux_ansatz_proved": True,
        "flux_quantization_proved": True,
        "flux_integer_n": 2,
        "q_LL_dimensionless": 0.5,
        "F2_0_m_minus_4": 8.0,
        "flux_state_provenance": "active_llbrane_flux_sector",
        "observational_fit_used": False,
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
    }


class ChiLLSuperselectionFluxReducerGateTests(unittest.TestCase):
    def test_missing_inputs_block(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            payload = build_payload(
                input_path=base / "missing.json",
                chi_output_path=base / "chi.json",
                orbit_output_path=base / "orbit.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["closure"]["chi_LL_abs_inverse_m_derived"])
        self.assertIn("derive_worldvolume_charge_quantum_q_LL", payload["next_required"])

    def test_forbidden_provenance_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            input_path = base / "flux.json"
            data = valid_input()
            data["flux_state_provenance"] = "planck fit"
            input_path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(
                input_path=input_path,
                chi_output_path=base / "chi.json",
                orbit_output_path=base / "orbit.json",
            )

        self.assertFalse(payload["gate_passed"])
        self.assertIn(
            "flux_state_provenance_missing_or_forbidden",
            payload["validation_errors"],
        )

    def test_valid_flux_sector_derives_chi_and_orbit_mass(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            input_path = base / "flux.json"
            chi_path = base / "chi.json"
            orbit_path = base / "orbit.json"
            input_path.write_text(json.dumps(valid_input()), encoding="utf-8")
            payload = build_payload(
                input_path=input_path,
                chi_output_path=chi_path,
                orbit_output_path=orbit_path,
                write_output=True,
            )
            self.assertTrue(chi_path.exists())
            self.assertTrue(orbit_path.exists())

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["closure"]["chi_LL_abs_inverse_m_derived"])
        computed = payload["computed"]
        expected_rs = 1.0
        expected_chi = 1.0 / (8.0 * math.pi)
        expected_mass = C_SI * C_SI / (2.0 * G_SI)
        self.assertAlmostEqual(computed["R_s_m"], expected_rs)
        self.assertAlmostEqual(computed["chi_LL_abs_inverse_m"], expected_chi)
        self.assertAlmostEqual(computed["M_bridge_kg"], expected_mass)


if __name__ == "__main__":
    unittest.main()
