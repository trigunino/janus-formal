import unittest

from scripts.build_p0_eft_janus_sigma_aps_parity_anomaly_cancellation_gate import build_payload


class P0EFTJanusSigmaAPSParityAnomalyCancellationGateTests(unittest.TestCase):
    def test_z2_tunnel_pairing_cancels_global_parity_anomaly(self):
        payload = build_payload()

        self.assertTrue(payload["sigma_parity_anomaly_cancellation_closed"])
        self.assertTrue(payload["parity_package"]["z2_tunnel_pairing_declared"])
        self.assertTrue(payload["parity_package"]["paired_boundary_orientation_reversal_declared"])
        self.assertTrue(payload["parity_package"]["paired_dirac_determinant_phase_opposite"])
        self.assertTrue(payload["parity_package"]["parity_anomaly_contributions_cancel_pairwise"])
        self.assertTrue(payload["sigma_aps_boundary_pin_lift_closed"])


if __name__ == "__main__":
    unittest.main()
