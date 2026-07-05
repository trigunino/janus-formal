import unittest

from scripts.build_p0_eft_janus_z2_sigma_spinor_soldering_equivariance_from_boundary_variation_gate import (
    build_payload,
)


class SpinorSolderingEquivarianceFromBoundaryVariationGateTests(unittest.TestCase):
    def test_gate_reduces_equivariance_to_spinor_boundary_residual(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["declared"]["local_U_Z2_sigma_imported"])
        self.assertTrue(payload["declared"]["spinor_soldering_condition_declared"])
        self.assertFalse(
            payload["physical_spinor_equivariance_from_boundary_variation_ready"]
        )
        self.assertEqual(
            payload["primary_blocker"],
            "spinor_soldering_boundary_variation_residual",
        )

    def test_no_free_spinor_boundary_shortcut_is_allowed(self):
        payload = build_payload()

        self.assertIn("free spinor phase", payload["forbidden"])
        self.assertIn("fit spinor residual coefficient", payload["forbidden"])
        self.assertFalse(payload["closure"]["R_psi_explicit_from_boundary_variation"])
        self.assertIn(
            "compute_R_psi_from_projected_dirac_boundary_variation",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
