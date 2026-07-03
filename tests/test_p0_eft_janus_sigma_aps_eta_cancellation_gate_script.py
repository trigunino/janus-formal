import unittest

from scripts.build_p0_eft_janus_sigma_aps_eta_cancellation_gate import build_payload


class P0EFTJanusSigmaAPSEtaCancellationGateTests(unittest.TestCase):
    def test_eta_zero_mode_cancellation_closed_but_parity_anomaly_open(self):
        payload = build_payload()

        self.assertTrue(payload["sigma_eta_zero_mode_cancellation_closed"])
        self.assertTrue(payload["eta_package"]["sigma_dirac_spectrum_paired"])
        self.assertTrue(payload["eta_package"]["sigma_dirac_kernel_trivial"])
        self.assertTrue(payload["eta_package"]["eta_invariant_zero"])
        self.assertTrue(payload["eta_package"]["zero_mode_dimension_zero"])
        self.assertTrue(payload["parity_anomaly_cancellation_deferred_to_parity_gate"])


if __name__ == "__main__":
    unittest.main()
