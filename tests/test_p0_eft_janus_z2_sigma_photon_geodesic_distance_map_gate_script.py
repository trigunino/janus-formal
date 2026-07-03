import unittest

from scripts.build_p0_eft_janus_z2_sigma_photon_geodesic_distance_map_gate import build_payload


class P0EFTJanusZ2SigmaPhotonGeodesicDistanceMapGateTests(unittest.TestCase):
    def test_sigma_photon_distance_map_is_derived_from_z2_sigma_background(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["photon_distance_lock_closed"])
        self.assertTrue(payload["sigma_photon_geodesic_map_derived"])
        self.assertTrue(payload["lock"]["background_equations_derived"])
        self.assertTrue(payload["lock"]["photon_null_geodesic_on_visible_projection"])
        self.assertTrue(payload["lock"]["etherington_guard_available"])
        self.assertTrue(payload["legacy_lcdm_distance_substitution_forbidden"])
        self.assertTrue(payload["archived_z4_distance_reuse_forbidden"])


if __name__ == "__main__":
    unittest.main()
