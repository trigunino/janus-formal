import unittest

from scripts.build_p0_eft_janus_z2_sigma_bulk_stress_normal_flux_cancellation_gate import build_payload


class P0EFTJanusZ2SigmaBulkStressNormalFluxCancellationGateTests(unittest.TestCase):
    def test_bulk_stress_normal_flux_cancellation_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["bulk_stress_normal_flux_cancellation_ledger_declared"])
        self.assertTrue(payload["declared"]["bulk_stress_of_a_gate_declared"])
        self.assertTrue(payload["declared"]["Z2_flux_cancellation_declared"])

    def test_cancellation_waits_for_bulk_stress_and_normals(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["bulk_stress_plus_of_a_ready"])
        self.assertFalse(payload["closure"]["Sigma_normals_ready"])
        self.assertFalse(payload["bulk_stress_normal_flux_cancellation_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertIn("bulk_stress_of_a", payload["upstream_frontiers"])
        self.assertEqual(
            payload["upstream_frontiers"]["bulk_stress_of_a"]["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertIn(
            "bulk_stress_plus_of_a_ready",
            payload["nearest_bulk_stress_flux_frontier"]["blocks"],
        )
        self.assertTrue(payload["nearest_bulk_stress_flux_frontier"]["diagnostic_only"])
        self.assertIn("prove_or_reject_Z2_flux_cancellation", payload["next_required"])

    def test_bibliography_uses_primary_thin_shell_sources(self):
        payload = build_payload()

        self.assertTrue(payload["source_links"])
        self.assertTrue(any("10.1007/BF02710419" in link for link in payload["source_links"]))
        self.assertTrue(any("arxiv.org" in link for link in payload["source_links"]))
        self.assertFalse(any("shoutwiki" in link.lower() for link in payload["source_links"]))


if __name__ == "__main__":
    unittest.main()
