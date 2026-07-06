from __future__ import annotations

import unittest

from scripts.run_p0_eft_janus_z2_sigma_surface_hk_geometry_materialization import (
    build_payload,
)


class SurfaceHKGeometryMaterializationTests(unittest.TestCase):
    def test_materialization_reports_first_blocker(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["steps"])
        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        if not payload["gate_passed"]:
            self.assertNotEqual(payload["primary_blocker"], "none")
            self.assertFalse(payload["surface_hk_geometry_materialized"])


if __name__ == "__main__":
    unittest.main()
