import math
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import build_p0_eft_janus_z2_sigma_area_flux_dual_closure_gate as dual


def route_a_payload(ratio: float, n: int = 2) -> dict:
    return {
        "status": "route-a-test",
        "route_a_origin_ready": True,
        "lambda_F2_over_q_LL_m_minus_2": ratio,
        "will_flux_radius_payload": {"flux_integer_n": n},
    }


def route_b_payload(radius: float) -> dict:
    return {
        "status": "route-b-test",
        "chi_LL_prediction_ready": True,
        "R_s_m": radius,
    }


class AreaFluxDualClosureGateTests(unittest.TestCase):
    def test_blocks_when_both_routes_missing(self):
        with tempfile.TemporaryDirectory() as tmp:
            missing = Path(tmp) / "missing.json"
            with patch.object(dual, "route_a", return_value={"status": "a", "route_a_origin_ready": False}), patch.object(
                dual, "route_b", return_value={"status": "b", "chi_LL_prediction_ready": False}
            ):
                payload = dual.build_payload(route_a_input=missing)

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["area_flux_dual_closure_ready"])
        self.assertIn("route_b_not_ready", payload["blocked_by"])

    def test_compatible_a_and_b_routes_close(self):
        radius = 4.0
        n = 2
        ratio = radius * radius / (math.sqrt(8.0) * n)
        with tempfile.TemporaryDirectory() as tmp:
            missing = Path(tmp) / "missing.json"
            with patch.object(dual, "route_a", return_value=route_a_payload(ratio, n)), patch.object(
                dual, "route_b", return_value=route_b_payload(radius)
            ):
                payload = dual.build_payload(route_a_input=missing)

        self.assertTrue(payload["area_flux_dual_closure_ready"])
        self.assertTrue(payload["comparison"]["compatible"])
        self.assertAlmostEqual(payload["lambda_F2_over_q_LL_from_route_b"], ratio)

    def test_incompatible_a_and_b_routes_do_not_close(self):
        with tempfile.TemporaryDirectory() as tmp:
            missing = Path(tmp) / "missing.json"
            with patch.object(dual, "route_a", return_value=route_a_payload(1.0, 2)), patch.object(
                dual, "route_b", return_value=route_b_payload(4.0)
            ):
                payload = dual.build_payload(route_a_input=missing)

        self.assertFalse(payload["area_flux_dual_closure_ready"])
        self.assertFalse(payload["comparison"]["compatible"])


if __name__ == "__main__":
    unittest.main()
