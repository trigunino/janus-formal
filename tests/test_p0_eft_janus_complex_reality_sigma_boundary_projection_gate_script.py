import unittest

from scripts.build_p0_eft_janus_complex_reality_sigma_boundary_projection_gate import (
    build_payload,
)


class ComplexRealitySigmaBoundaryProjectionGateTests(unittest.TestCase):
    def test_symbolic_projection_is_derived(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(
            payload[
                "sigma_boundary_to_complex_poincare_projection_symbolic_ready"
            ]
        )
        self.assertFalse(payload["alpha_generated_now"])
        self.assertIn(
            "symbolic_projection_deltaSigma_to_gamma",
            payload["what_this_closes"],
        )
        self.assertIn(
            "complex_Poincare_generator_ZSigma_formula",
            payload["what_this_closes"],
        )

    def test_active_nonzero_density_remains_blocked(self):
        payload = build_payload()

        self.assertFalse(
            payload["sigma_boundary_to_complex_poincare_projection_active_ready"]
        )
        self.assertFalse(payload["KKS_boundary_density_evaluable_now"])
        self.assertFalse(payload["KKS_boundary_density_nonzero"])
        self.assertIn(
            "nontrivial_boundary_variation_basis_ready",
            payload["still_missing_for_nonzero_density"],
        )
        self.assertEqual(payload["next_gate"], "ComplexRealityBoundaryVariationBasisGate")


if __name__ == "__main__":
    unittest.main()
