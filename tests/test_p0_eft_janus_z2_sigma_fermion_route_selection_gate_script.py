import unittest

from scripts.build_p0_eft_janus_z2_sigma_fermion_route_selection_gate import build_payload


class P0EFTJanusZ2SigmaFermionRouteSelectionGateTests(unittest.TestCase):
    def test_route_selection_is_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["fermion_route_selection_ready"])
        self.assertEqual(payload["selected_route"], "Dirac_gas_spinorial")
        self.assertTrue(payload["declared"]["no_fluid_route_chosen_by_fit"])

    def test_weyssenhoff_is_not_primitive_route(self):
        payload = build_payload()

        self.assertEqual(payload["weyssenhoff_status"], "coarse_graining_only_not_primitive_route")
        self.assertIn("derive_Dirac_fermion_number_density_of_a", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
