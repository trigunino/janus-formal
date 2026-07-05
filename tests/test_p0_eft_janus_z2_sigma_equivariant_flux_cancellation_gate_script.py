import unittest

from scripts.build_p0_eft_janus_z2_sigma_equivariant_flux_cancellation_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaEquivariantFluxCancellationGateTests(unittest.TestCase):
    def test_equivariant_flux_cancellation_is_conditional(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["algebraic_cancellation_theorem_declared"])
        self.assertFalse(payload["z2_flux_cancellation_derived"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "Z2_equivariant_embedding_derived")

    def test_cancellation_requires_geometric_and_stress_equivariance(self):
        payload = build_payload()
        closure = payload["closure"]

        self.assertFalse(closure["Z2_equivariant_embedding_derived"])
        self.assertTrue(closure["coorientation_ready"])
        self.assertFalse(closure["Sigma_tangents_ready"])
        self.assertFalse(closure["Sigma_normals_ready"])
        self.assertFalse(closure["Z2_stress_equivariance_derived"])
        self.assertIn("stress_equivariance", payload["upstream_frontiers"])
        self.assertEqual(
            payload["upstream_frontiers"]["stress_equivariance"]["primary_blocker"],
            "plus_rho_p_of_a_ready",
        )
        self.assertIn("normal_reversal", payload["formulas"])
        self.assertIn("tangent_transport", payload["formulas"])
        self.assertIn("cancellation", payload["formulas"])

    def test_next_required_targets_real_proof_inputs(self):
        payload = build_payload()

        self.assertIn("prove_Z2_equivariance_of_embedding", payload["next_required"])
        self.assertIn("derive_Z2_stress_equivariance_T_minus_equals_pushforward_T_plus", payload["next_required"])
        self.assertIn("then_use_algebraic_cancellation_to_set_F_a_Z2Sigma_zero", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
