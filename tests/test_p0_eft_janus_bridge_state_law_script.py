import unittest

from scripts.build_p0_eft_janus_bridge_state_law_opening_gate import build_payload


class JanusBridgeStateLawTests(unittest.TestCase):
    def test_branch_opens_without_alpha_fit(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["rules"]["no_direct_alpha_fit"])
        self.assertTrue(payload["rules"]["no_invented_sigma_density"])
        self.assertFalse(payload["chi_LL_selected_no_fit"])

    def test_three_candidate_routes_are_declared(self):
        payload = build_payload()
        route_ids = {row["id"] for row in payload["candidate_routes"]}

        self.assertEqual(len(route_ids), 3)
        self.assertIn("null_boundary_noether_charge", route_ids)
        self.assertIn("LL_worldvolume_flux_sector", route_ids)
        self.assertIn("PT_minimal_quantum_state", route_ids)


if __name__ == "__main__":
    unittest.main()
