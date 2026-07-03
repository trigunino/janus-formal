import unittest

from scripts.build_p0_eft_janus_z2_sigma_throat_radius_block_expansion_gate import build_payload


class P0EFTJanusZ2SigmaThroatRadiusBlockExpansionGateTests(unittest.TestCase):
    def test_block_ledger_is_declared_without_radius_fit(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["throat_radius_block_ledger_declared"])
        self.assertTrue(payload["declared"]["no_observational_radius_fit"])
        self.assertIn("E_CartanGHY", payload["block_sum"])

    def test_radial_blocks_are_not_reduced_or_solved_yet(self):
        payload = build_payload()

        self.assertTrue(payload["reduced"]["Cartan_GHY_radial_block_reduced"])
        self.assertTrue(payload["reduced"]["Holst_Nieh_Yan_radial_block_reduced"])
        self.assertTrue(payload["reduced"]["tunnel_junction_radial_block_reduced"])
        self.assertFalse(payload["all_radial_blocks_reduced"])
        self.assertFalse(payload["throat_radius_block_expansion_ready"])
        self.assertFalse(payload["throat_radius_solved_from_blocks"])
        self.assertIn("reduce_matter_flux_radial_block_E_flux", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
