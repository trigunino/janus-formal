from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_surface_hk_geometry_dual_route_gate import (
    build_payload,
)


class SurfaceHKGeometryDualRouteGateTests(unittest.TestCase):
    def test_reports_route_status_without_promoting_missing_geometry(self) -> None:
        payload = build_payload()

        self.assertIn(payload["selected_route"], {
            "surface_hk_radial_tensor_geometry_inputs",
            "cartan_ghy_embedding_stencil_tensor_primitives",
            "normal_flow_K_ab_R_nabn",
            "none",
        })
        if not payload["gate_passed"]:
            self.assertEqual(
                payload["primary_blocker"],
                "active_surface_tensor_or_stencil_or_normal_flow_geometry",
            )


if __name__ == "__main__":
    unittest.main()
