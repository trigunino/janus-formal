import unittest

from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_matter_current_gate import build_payload


class P0EFTJanusZ2SigmaProjectedDiracMatterCurrentGateTests(unittest.TestCase):
    def test_projected_dirac_matter_current_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["projected_dirac_matter_current_ledger_declared"])
        self.assertTrue(payload["declared"]["U1_vector_symmetry_declared"])
        self.assertTrue(payload["declared"]["Z2_projected_current_declared"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")

    def test_projected_current_closes_from_projected_dirac_action(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["projected_Dirac_action_ready"])
        self.assertTrue(payload["closure"]["Z2_projected_current_ready"])
        self.assertTrue(payload["projected_dirac_matter_current_ready"])
        self.assertIn("projected_dirac_action_reduction", payload["upstream_frontiers"])
        self.assertIn("plus_minus_matter_current", payload["upstream_frontiers"])
        self.assertTrue(payload["upstream_frontiers"]["projected_dirac_action_reduction"]["ready"])
        self.assertTrue(payload["upstream_frontiers"]["plus_minus_matter_current"]["ready"])

    def test_bibliography_uses_primary_sources(self):
        payload = build_payload()

        self.assertTrue(payload["source_links"])
        self.assertFalse(any("wikipedia.org" in link for link in payload["source_links"]))
        self.assertTrue(any("arxiv.org" in link for link in payload["source_links"]))
        self.assertTrue(any("doi" in link or "link.aps.org" in link for link in payload["source_links"]))


if __name__ == "__main__":
    unittest.main()
