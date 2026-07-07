import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_chi_ll_route_a_lambda_over_q_origin_gate import (
    build_payload,
)


class RouteALambdaOverQOriginGateTests(unittest.TestCase):
    def test_default_blocks_without_origin(self):
        payload = build_payload(Path("missing-route-a.json"))

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["route_a_origin_ready"])
        self.assertIn("origin_route_declared", payload["blocked_by"])

    def test_canonical_connection_route_writes_will_radius_payload(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            input_path = base / "route_a.json"
            output_path = base / "will_radius.json"
            input_path.write_text(
                json.dumps(
                    {
                        "origin_route": "canonical_connection_normalization",
                        "A_LL_is_connection_on_global_U1_bundle": True,
                        "minimal_charge_unit_derived": True,
                        "WILL_lambda_normalization_derived": True,
                        "lambda_F2_over_q_LL_m_minus_2": 0.5,
                        "flux_integer_n": 2,
                        "area_gauge": "physical_induced_S2_metric",
                        "provenance": "active_route_a_canonical_connection",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(input_path, output_path, write_output=True)

            self.assertTrue(output_path.exists())
            out = json.loads(output_path.read_text(encoding="utf-8"))

        self.assertTrue(payload["route_a_origin_ready"])
        self.assertEqual(out["lambda_F2_over_q_LL"], 0.5)
        self.assertEqual(out["flux_integer_n"], 2)
        self.assertEqual(out["power_p"], 0.5)

    def test_selected_route_must_have_own_required_derivations(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "route_a.json"
            path.write_text(
                json.dumps(
                    {
                        "origin_route": "PT_Noether_boundary_charge",
                        "PT_boundary_symplectic_potential_projected": True,
                        "Noether_charge_unit_derived": True,
                        "charge_to_LL_connection_map_derived": True,
                        "lambda_F2_over_q_LL_m_minus_2": 0.5,
                        "flux_integer_n": 2,
                        "area_gauge": "physical_induced_S2_metric",
                        "provenance": "active_route_a_pt_noether",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertFalse(payload["route_a_origin_ready"])
        self.assertIn("selected_origin_route_ready", payload["blocked_by"])

    def test_complete_pt_noether_route_is_accepted(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "route_a.json"
            path.write_text(
                json.dumps(
                    {
                        "origin_route": "PT_Noether_boundary_charge",
                        "PT_boundary_symplectic_potential_projected": True,
                        "Noether_charge_unit_derived": True,
                        "charge_to_LL_connection_map_derived": True,
                        "PT_Noether_radius_or_mass_charge_derived": True,
                        "lambda_F2_over_q_LL_m_minus_2": 0.5,
                        "flux_integer_n": 2,
                        "area_gauge": "physical_induced_S2_metric",
                        "provenance": "active_route_a_pt_noether",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertTrue(payload["route_a_origin_ready"])

    def test_observational_provenance_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "route_a.json"
            path.write_text(
                json.dumps(
                    {
                        "origin_route": "UV_action_dimensional_coupling",
                        "UV_length_or_mass_scale_derived": True,
                        "lambda_F2_from_UV_action_derived": True,
                        "q_LL_from_same_UV_sector_derived": True,
                        "lambda_F2_over_q_LL_m_minus_2": 0.5,
                        "flux_integer_n": 2,
                        "area_gauge": "physical_induced_S2_metric",
                        "provenance": "bao fit",
                    }
                ),
                encoding="utf-8",
            )
            payload = build_payload(path)

        self.assertFalse(payload["route_a_origin_ready"])
        self.assertIn("non_observational_provenance", payload["blocked_by"])


if __name__ == "__main__":
    unittest.main()
