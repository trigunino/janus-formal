import tempfile
import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z2_sigma_counterterm_lct_density_route_decision import (
    build_payload,
)


class CountertermLctDensityRouteDecisionTests(unittest.TestCase):
    def test_writes_obstruction_without_density_promotion(self):
        with tempfile.TemporaryDirectory() as tmp:
            obstruction = Path(tmp) / "obstruction.json"
            payload = build_payload(obstruction_path=obstruction)

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["decision"], "obstruction")
        self.assertFalse(payload["counterterm_local_density_action_inputs_written"])
        self.assertTrue(payload["counterterm_local_density_action_obstruction_written"])
        self.assertTrue(payload["bibliography_checked"])
        self.assertTrue(payload["pulled_action_bridge"]["closed"])
        self.assertEqual(
            payload["pulled_action_bridge"]["primary_blocker"],
            "explicit_L_ct_coefficient_expansion",
        )
        self.assertIn("compute_R_h_ab_R_K_ab_R_chi_from_S_ct_variation", payload["next_required"])

    def test_all_routes_are_rejected_until_action_bridge_exists(self):
        payload = build_payload()

        self.assertTrue(payload["routes"])
        self.assertTrue(all(not row["admissible_as_active_L_ct"] for row in payload["routes"]))
        route_names = {row["route"] for row in payload["routes"]}
        self.assertIn("cartan_ghy_duplicate", route_names)
        self.assertIn("pure_holst_nieh_yan", route_names)
        self.assertIn("volume_solder_logdet", route_names)
        self.assertIn("transgression_boundary_action", route_names)


if __name__ == "__main__":
    unittest.main()
