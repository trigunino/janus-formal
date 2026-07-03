import unittest

from scripts.build_p0_eft_janus_sigma_aps_local_throat_model_gate import build_payload


class P0EFTJanusSigmaAPSLocalThroatModelGateTests(unittest.TestCase):
    def test_local_throat_aps_package_closed_but_global_lift_open(self):
        payload = build_payload()

        self.assertTrue(payload["sigma_aps_local_package_closed"])
        self.assertTrue(payload["local"]["induced_pin_structure_available_locally"])
        self.assertTrue(payload["local"]["aps_boundary_projector_available_locally"])
        self.assertTrue(payload["local"]["fredholm_domain_available_locally"])
        self.assertTrue(payload["global"]["eta_zero_mode_cancellation_deferred_to_eta_gate"])
        self.assertFalse(payload["global"]["parity_anomaly_cancellation_global_closed"])
        self.assertFalse(payload["sigma_aps_boundary_pin_lift_closed"])


if __name__ == "__main__":
    unittest.main()
