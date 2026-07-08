import unittest

from scripts.build_p0_eft_janus_llbrane_bridge_source_gate import build_payload


class JanusLLBraneBridgeSourceTests(unittest.TestCase):
    def test_bridge_mass_route_is_real_but_tension_missing(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["closed_by_bibliography"]["bridge_mass_can_depend_on_LL_tension"])
        self.assertFalse(payload["janus_map"]["chi_LL_derived_from_Janus"])
        self.assertFalse(payload["no_fit_alpha_generated"])

    def test_chi_routes_are_explicit(self):
        payload = build_payload()
        route_ids = {row["id"] for row in payload["candidate_routes_to_chi_LL"]}

        self.assertIn("PT_boundary_condition", route_ids)
        self.assertIn("LL_auxiliary_flux_quantization", route_ids)
        self.assertIn("global_Noether_charge_matching", route_ids)


if __name__ == "__main__":
    unittest.main()
