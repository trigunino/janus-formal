import unittest

from scripts.build_p0_eft_janus_z2_sigma_background_bibliography_gate import build_payload


class P0EFTJanusZ2SigmaBackgroundBibliographyGateTests(unittest.TestCase):
    def test_bibliography_supports_but_does_not_close_background(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["janus_projective_tunnel_topology_source_found"])
        self.assertTrue(payload["janus_bimetric_flrw_source_found"])
        self.assertTrue(payload["junction_boundary_formalism_source_found"])
        self.assertTrue(payload["einstein_cartan_holst_cosmology_source_found"])
        self.assertFalse(payload["complete_z2_sigma_background_equations_found"])
        self.assertTrue(payload["local_derivation_required"])
        self.assertTrue(payload["must_derive_projected_sigma_background_locally"])


if __name__ == "__main__":
    unittest.main()
