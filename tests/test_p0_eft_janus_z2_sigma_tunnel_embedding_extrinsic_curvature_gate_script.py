import unittest

from scripts.build_p0_eft_janus_z2_sigma_tunnel_embedding_extrinsic_curvature_gate import build_payload


class P0EFTJanusZ2SigmaTunnelEmbeddingExtrinsicCurvatureGateTests(unittest.TestCase):
    def test_structural_embedding_extrinsic_curvature_is_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["extrinsic_curvature_structural_closure_ready"])
        self.assertTrue(payload["structural"]["DeltaK_s_from_K_plus_minus_ready"])
        self.assertIn("K_ab^pm", payload["definitions"]["extrinsic_curvature"])

    def test_scale_factor_embedding_functions_remain_open(self):
        payload = build_payload()

        self.assertFalse(payload["scale_factor"]["tunnel_embedding_functions_of_a_ready"])
        self.assertFalse(payload["scale_factor"]["DeltaK_s_of_a_ready"])
        self.assertFalse(payload["extrinsic_curvature_scale_factor_closure_ready"])
        self.assertIn(
            "pass_active_tunnel_embedding_of_a_gate",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
