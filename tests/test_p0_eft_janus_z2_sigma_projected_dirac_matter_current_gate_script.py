import unittest

from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_matter_current_gate import build_payload


class P0EFTJanusZ2SigmaProjectedDiracMatterCurrentGateTests(unittest.TestCase):
    def test_projected_dirac_matter_current_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["projected_dirac_matter_current_ledger_declared"])
        self.assertTrue(payload["declared"]["U1_vector_symmetry_declared"])
        self.assertTrue(payload["declared"]["Z2_projected_current_declared"])

    def test_projected_current_waits_for_projected_dirac_action(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["projected_Dirac_action_ready"])
        self.assertFalse(payload["closure"]["Z2_projected_current_ready"])
        self.assertFalse(payload["projected_dirac_matter_current_ready"])
        self.assertIn("pass_projected_Dirac_action_reduction_gate", payload["next_required"])

    def test_bibliography_uses_primary_sources(self):
        payload = build_payload()

        self.assertTrue(payload["source_links"])
        self.assertFalse(any("wikipedia.org" in link for link in payload["source_links"]))
        self.assertTrue(any("arxiv.org" in link for link in payload["source_links"]))
        self.assertTrue(any("doi" in link or "link.aps.org" in link for link in payload["source_links"]))


if __name__ == "__main__":
    unittest.main()
