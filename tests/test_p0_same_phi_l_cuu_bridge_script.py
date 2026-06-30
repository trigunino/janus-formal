from __future__ import annotations

import unittest

from scripts.build_p0_same_phi_l_cuu_bridge import build_payload


class P0SamePhiLCuuBridgeTests(unittest.TestCase):
    def test_single_cross_dust_bridge_closed_but_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["target_identity"], "h a_to = h C(u_to,u_to)")
        self.assertTrue(payload["same_phi_l_bridge_closed"])
        self.assertTrue(payload["source_geodesic_anchor_closed"])
        self.assertTrue(payload["single_cross_dust_cuu_force_closed"])
        self.assertFalse(payload["dynamic_phi_l_selection_closed"])
        self.assertFalse(payload["mirror_consistency_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_derivation_contains_same_map_connection_split_and_geodesic_anchor(self) -> None:
        text = " ".join(row["claim"] + " " + row["formula"] for row in build_payload()["derivation_steps"])

        self.assertIn("one declared phi/L", text)
        self.assertIn("connection difference", text)
        self.assertIn("v^a D_source_a v^b = 0", text)
        self.assertIn("h a_to = h C", text)

    def test_remaining_rows_keep_dynamic_mirror_integrability_and_pressure_open(self) -> None:
        remaining = " ".join(build_payload()["remaining_rows"])

        self.assertIn("dynamically", remaining)
        self.assertIn("mirror consistency", remaining)
        self.assertIn("integrability", remaining)
        self.assertIn("pressure/Pi", remaining)


if __name__ == "__main__":
    unittest.main()
