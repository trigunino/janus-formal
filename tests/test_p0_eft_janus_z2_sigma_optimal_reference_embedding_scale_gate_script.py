import unittest

from scripts.build_p0_eft_janus_z2_sigma_optimal_reference_embedding_scale_gate import (
    build_payload,
)


class OptimalReferenceEmbeddingScaleGateTests(unittest.TestCase):
    def test_optimal_reference_does_not_fix_absolute_throat_scale(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["reference_prescription_ready"])
        self.assertFalse(payload["absolute_scale_fixed"])
        self.assertEqual(
            payload["allowed_conclusion"],
            "reference_fixes_zero_and_k_ref_not_RSigma",
        )
        self.assertEqual(
            payload["forbidden_conclusion"],
            "reference_extremization_alone_derives_absolute_RSigma",
        )
        self.assertIn(
            "derive_absolute_R_Sigma_from_global_Janus_tunnel_or_boundary_metric",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
