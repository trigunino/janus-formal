import unittest

from scripts.build_p0_eft_janus_z2_sigma_distance_bao_bibliography_gate import build_payload


class P0EFTJanusZ2SigmaDistanceBAOBibliographyGateTests(unittest.TestCase):
    def test_bibliography_requires_local_sigma_distance_and_rd_derivation(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["standard_flrw_distance_source_found"])
        self.assertTrue(payload["curved_transverse_distance_source_found"])
        self.assertTrue(payload["etherington_reciprocity_source_found"])
        self.assertTrue(payload["bao_sound_horizon_source_found"])
        self.assertTrue(payload["photon_baryon_drag_source_found"])
        self.assertIn("curved_transverse_comoving_distance_Sk_chi", payload["sources"]["hogg_distance_measures"]["supports"])
        self.assertFalse(payload["complete_sigma_photon_distance_map_found"])
        self.assertFalse(payload["complete_z2_sigma_sound_ruler_found"])
        self.assertTrue(payload["local_distance_and_ruler_derivation_required"])
        self.assertTrue(payload["must_derive_sigma_photon_geodesic_map_locally"])
        self.assertTrue(payload["must_derive_z2_sigma_rd_locally"])


if __name__ == "__main__":
    unittest.main()
