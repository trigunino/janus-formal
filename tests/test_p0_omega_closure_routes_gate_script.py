from __future__ import annotations

import unittest

from scripts.build_p0_omega_closure_routes_gate import build_payload


class P0OmegaClosureRoutesGateTests(unittest.TestCase):
    def test_routes_gate_is_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "omega-closure-routes-open")
        self.assertTrue(payload["source_omega_u_zero_route_available"])
        self.assertTrue(payload["omega_u_zero_source_derivation_target_available"])
        self.assertTrue(payload["projection_annihilation_route_available"])
        self.assertTrue(payload["omega_projection_annihilation_gate_available"])
        self.assertTrue(payload["mirror_inverse_route_required"])
        self.assertTrue(payload["same_l_omega_observable_route_required"])
        self.assertTrue(payload["no_fit_route_selection"])
        self.assertFalse(payload["omega_residual_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_routes_cover_zero_projection_mirror_and_observables(self) -> None:
        text = " ".join(row["route"] + row["condition"] for row in build_payload()["routes"])

        self.assertIn("Omega u=0", text)
        self.assertIn("projection", text)
        self.assertIn("Omega^T T+T Omega", text)
        self.assertIn("inverse-compatible", text)
        self.assertIn("K transport, Q_cross", text)


if __name__ == "__main__":
    unittest.main()
