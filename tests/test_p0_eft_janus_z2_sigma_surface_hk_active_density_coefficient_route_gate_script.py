from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_surface_hk_active_density_coefficient_route_gate import (
    build_payload,
)


class SurfaceHKActiveDensityCoefficientRouteGateTests(unittest.TestCase):
    def test_blocks_unless_active_coefficients_or_trace_targets_exist(self) -> None:
        payload = build_payload()

        if not payload["gate_passed"]:
            self.assertEqual(
                payload["primary_blocker"],
                "active_density_coefficients_or_active_residual_trace_targets",
            )
            self.assertIn("free_a0_a1_a2_a3", payload["forbidden"])
            self.assertIn("observational_fit_for_a_i", payload["forbidden"])


if __name__ == "__main__":
    unittest.main()
