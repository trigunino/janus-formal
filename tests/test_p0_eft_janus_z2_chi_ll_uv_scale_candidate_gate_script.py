import unittest

from scripts.build_p0_eft_janus_z2_chi_ll_uv_scale_candidate_gate import build_payload


class ChiLLUVScaleCandidateGateTests(unittest.TestCase):
    def test_uv_route_does_not_predict_chi_without_identification_theorem(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["chi_LL_uv_prediction_ready"])
        self.assertFalse(payload["R_s_uv_prediction_ready"])
        self.assertIn("R_s_equals_lP_or_area_gap_radius", payload["missing_theorems"])

    def test_holst_and_nieh_yan_do_not_supply_length_alone(self):
        candidates = build_payload()["candidate_scales"]

        self.assertEqual(candidates["Holst_Immirzi_gamma"]["verdict"], "dimensionless_coupling_only")
        self.assertEqual(
            candidates["Nieh_Yan_density"]["verdict"],
            "topological_or_boundary_without_state_scale",
        )

    def test_non_rustine_exits_are_explicit(self):
        routes = build_payload()["non_rustine_exit_routes"]

        self.assertIn("prove_throat_area_equals_quantum_area_gap", routes)
        self.assertIn("derive_fermion_condensate_or_spin_density_on_Sigma", routes)
        self.assertIn("derive_LL_gauge_action_normalization_from_UV_completion", routes)


if __name__ == "__main__":
    unittest.main()
