from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_pt67_regular_surface_gate import build_payload


class Z2PT67RegularSurfaceGateScriptTests(unittest.TestCase):
    def test_script_exports_regular_route_without_deltak(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["route"], "chapter_6_7_regular_PT_transfer_cross_term_surface")
        self.assertTrue(payload["raccord_to_regular_sigma_pipeline"]["h_ab_ready"])
        self.assertTrue(payload["raccord_to_regular_sigma_pipeline"]["K_ab_local_ready"])
        self.assertFalse(payload["raccord_to_regular_sigma_pipeline"]["DeltaK_plus_minus_ready"])


if __name__ == "__main__":
    unittest.main()
