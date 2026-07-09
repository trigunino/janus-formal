import unittest

from scripts.build_p0_eft_janus_projected_photon_baryon_plasma_frontier_gate import (
    build_payload,
)


class JanusProjectedPhotonBaryonPlasmaFrontierGateTests(unittest.TestCase):
    def test_formula_chain_is_ready_but_native_rd_is_blocked(self):
        payload = build_payload()

        self.assertTrue(all(payload["formula_chain"].values()))
        self.assertFalse(payload["native_rd_evaluated"])
        self.assertFalse(payload["native_bao_prediction_ready"])
        self.assertTrue(payload["current_bottom_reached"])

    def test_missing_inputs_are_active_not_lcdm_shortcuts(self):
        payload = build_payload()

        self.assertIn(
            "active_baryon_number_density0_m3_Z2Sigma",
            payload["missing_active_inputs"],
        )
        self.assertIn("Planck/Lambda-CDM r_d reuse", payload["forbidden_shortcuts"])
        self.assertFalse(payload["physical_input_obligation"]["passed"])
        self.assertFalse(payload["scale_free_plasma_primitive"]["passed"])

    def test_other_routes_are_documented_as_blocked(self):
        payload = build_payload()

        routes = {item["route"] for item in payload["other_route_blockers"]}
        self.assertEqual(
            routes,
            {
                "orbifold_redshift_map",
                "early_time_sister_branch",
                "topological_spectrum_ruler",
            },
        )


if __name__ == "__main__":
    unittest.main()
