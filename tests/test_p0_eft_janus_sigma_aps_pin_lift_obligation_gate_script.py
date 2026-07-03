import unittest

from scripts.build_p0_eft_janus_sigma_aps_pin_lift_obligation_gate import build_payload


class P0EFTJanusSigmaAPSPinLiftObligationGateTests(unittest.TestCase):
    def test_sigma_aps_pin_lift_obligations_declared_and_closed(self):
        payload = build_payload()

        self.assertTrue(payload["sigma_aps_pin_lift_obligations_declared"])
        self.assertTrue(payload["obligations"]["rp4_base_pin_plus_computed"])
        self.assertTrue(payload["obligations"]["rp4_base_pin_minus_obstructed"])
        self.assertTrue(payload["obligations"]["sigma_induced_pin_structure_declared"])
        self.assertTrue(payload["obligations"]["aps_boundary_projector_declared"])
        self.assertTrue(payload["obligations"]["fredholm_domain_declared"])
        self.assertTrue(payload["sigma_aps_boundary_pin_lift_closed"])
        self.assertTrue(payload["aps_pin_closure_allowed"])


if __name__ == "__main__":
    unittest.main()
