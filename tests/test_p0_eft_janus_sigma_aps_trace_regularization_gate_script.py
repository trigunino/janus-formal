import unittest

from scripts.build_p0_eft_janus_sigma_aps_trace_regularization_gate import build_payload


class P0EFTJanusSigmaAPSTraceRegularizationGateTests(unittest.TestCase):
    def test_trace_regularization_closed_after_sigma_aps_package(self):
        payload = build_payload()

        self.assertTrue(payload["sigma_aps_boundary_pin_lift_closed"])
        self.assertTrue(payload["clifford_trace_normalization_declared"])
        self.assertTrue(payload["aps_heat_kernel_regularization_declared"])
        self.assertTrue(payload["trace_regularization_standard_global"])
        self.assertTrue(payload["sigma_aps_trace_regularization_closed"])


if __name__ == "__main__":
    unittest.main()
