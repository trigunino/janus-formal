import unittest

from scripts.build_p0_eft_janus_around_sigma_z2_cycle_transport_gate import build_payload


class P0EFTJanusAroundSigmaZ2CycleTransportGateTests(unittest.TestCase):
    def test_around_sigma_maps_to_z2_generator_without_cyclic_z4(self):
        payload = build_payload()

        self.assertTrue(payload["tunnel_throat_sigma_defined"])
        self.assertTrue(payload["around_sigma_cycle_defined"])
        self.assertTrue(payload["quotient_projection_to_z2_defined"])
        self.assertTrue(payload["around_sigma_maps_to_z2_generator"])
        self.assertFalse(payload["cyclic_z4_monodromy_required"])
        self.assertTrue(payload["around_sigma_z2_transport_closed"])


if __name__ == "__main__":
    unittest.main()
