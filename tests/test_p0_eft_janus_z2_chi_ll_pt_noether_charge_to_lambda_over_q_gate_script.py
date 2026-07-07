import json
import math
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_chi_ll_pt_noether_charge_to_lambda_over_q_gate import (
    C_SI,
    G_SI,
    build_payload,
)


def valid_input() -> dict:
    return {
        "PT_boundary_symplectic_potential_projected": True,
        "Noether_charge_unit_derived": True,
        "charge_to_LL_connection_map_derived": True,
        "PT_energy_sign_reversal_proved": True,
        "M_bridge_kg": 2.0,
        "flux_integer_n": 3,
        "area_gauge": "physical_induced_S2_metric",
        "provenance": "active_pt_noether_mass_state",
    }


class PTNoetherChargeToLambdaOverQGateTests(unittest.TestCase):
    def test_default_blocks_without_charge(self):
        payload = build_payload(Path("missing-pt-noether.json"))

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["pt_noether_lambda_over_q_ready"])
        self.assertIn("radius_or_bridge_charge_available", payload["blocked_by"])

    def test_mass_charge_derives_ratio_and_route_a_payload(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            input_path = base / "pt_noether.json"
            output_path = base / "route_a.json"
            input_path.write_text(json.dumps(valid_input()), encoding="utf-8")
            payload = build_payload(input_path, output_path, write_output=True)
            out = json.loads(output_path.read_text(encoding="utf-8"))

        expected_rs = 2.0 * G_SI * 2.0 / C_SI**2
        expected_ratio = expected_rs * expected_rs / (math.sqrt(8.0) * 3.0)
        self.assertTrue(payload["pt_noether_lambda_over_q_ready"])
        self.assertAlmostEqual(payload["R_s_m"], expected_rs)
        self.assertAlmostEqual(payload["lambda_F2_over_q_LL_m_minus_2"], expected_ratio)
        self.assertEqual(out["origin_route"], "PT_Noether_boundary_charge")
        self.assertEqual(out["flux_integer_n"], 3)

    def test_radius_input_derives_ratio_without_mass(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "pt_noether.json"
            data = valid_input()
            data.pop("M_bridge_kg")
            data["R_s_m"] = 4.0
            data["flux_integer_n"] = 2
            path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(path)

        self.assertTrue(payload["pt_noether_lambda_over_q_ready"])
        self.assertEqual(payload["radius_source"], "R_s_m")
        self.assertAlmostEqual(payload["lambda_F2_over_q_LL_m_minus_2"], 16.0 / (math.sqrt(8.0) * 2.0))

    def test_observational_provenance_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "pt_noether.json"
            data = valid_input()
            data["provenance"] = "planck fit"
            path.write_text(json.dumps(data), encoding="utf-8")
            payload = build_payload(path)

        self.assertFalse(payload["pt_noether_lambda_over_q_ready"])
        self.assertIn("non_observational_provenance", payload["blocked_by"])


if __name__ == "__main__":
    unittest.main()
