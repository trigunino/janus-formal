import unittest

from scripts.build_p0_eft_janus_projective_tunnel_interface import build_payload


class P0EFTJanusProjectiveTunnelInterfaceTests(unittest.TestCase):
    def test_projective_tunnel_supplies_sigma_cycle(self):
        payload = build_payload()

        interface = payload["projective_tunnel_interface"]
        self.assertTrue(interface["projective_tunnel_closed"])
        self.assertTrue(interface["around_sigma_cycle_defined"])
        self.assertTrue(interface["quotient_projection_to_z2_defined"])
        self.assertTrue(interface["around_sigma_maps_to_generator"])
        self.assertTrue(interface["supplies_singular_cycle_transport"])
        self.assertTrue(payload["z2_holonomy_path_available"])

    def test_resolved_shadow_is_torus_to_klein_not_boy_surface(self):
        payload = build_payload()

        topology = payload["projective_tunnel_topology"]
        self.assertTrue(topology["torus_double_cover_shadow_defined"])
        self.assertTrue(topology["klein_bottle_quotient_shadow_defined"])
        self.assertTrue(topology["torus_to_klein_two_fold_cover"])
        self.assertTrue(topology["resolved_tunnel_shadow_not_boy_surface"])
        self.assertEqual(payload["resolved_2d_shadow"], "T2_to_Klein_bottle")

    def test_cyclic_z4_is_blocked_until_monodromy(self):
        payload = build_payload()

        z4_lift = payload["lifted_z4_monodromy"]
        self.assertTrue(z4_lift["tunnel_loop_defined"])
        self.assertTrue(z4_lift["sector_bundle_defined"])
        self.assertFalse(z4_lift["monodromy_defined"])
        self.assertFalse(z4_lift["monodromy_fourth_power_identity"])
        self.assertFalse(z4_lift["cyclic_z4_derived"])
        self.assertTrue(payload["cyclic_z4_path_blocked"])


if __name__ == "__main__":
    unittest.main()
