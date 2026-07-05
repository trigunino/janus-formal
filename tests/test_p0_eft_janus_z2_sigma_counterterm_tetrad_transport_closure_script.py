import unittest

from scripts.derive_p0_eft_janus_z2_sigma_counterterm_tetrad_transport_closure import (
    build_payload,
)


class P0EFTJanusZ2SigmaCountertermTetradTransportClosureTests(unittest.TestCase):
    def test_closes_deltae_to_deltaK_and_torsion_pullback_locally(self):
        payload = build_payload()
        closure = payload["closure"]

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(closure["tetrad_transport_closed_without_RSigma_values"])
        self.assertEqual(
            closure["extrinsic_curvature_transport"]["K_ab"],
            "1/2 partial_R h_ab = R_Sigma q_ab",
        )
        self.assertEqual(closure["extrinsic_curvature_transport"]["K_trace"], "3 / R_Sigma")
        self.assertEqual(
            closure["extrinsic_curvature_transport"]["partial_R_K_trace"],
            "-3 / R_Sigma^2",
        )
        self.assertTrue(closure["torsion_pullback_transport"]["torsion_pullback_value_zero"])
        self.assertTrue(closure["counterterm_residual_channel"]["tetrad_residual_channel_closed"])
        self.assertIn("R_K^{ab}", closure["counterterm_residual_channel"]["still_requires_residual_coefficients"])


if __name__ == "__main__":
    unittest.main()
