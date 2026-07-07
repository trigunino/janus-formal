import unittest

from scripts.build_p0_eft_janus_z2_alpha_selection_route_coverage_audit import build_payload


class AlphaSelectionRouteCoverageAuditTests(unittest.TestCase):
    def test_coverage_audit_runs_and_finds_no_selector(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["route_count"], 12)
        self.assertFalse(payload["alpha_no_fit_selector_found"])
        self.assertEqual(payload["no_fit_selector_ready_route_ids"], [])
        self.assertIsInstance(payload["missing_route_ids"], list)


if __name__ == "__main__":
    unittest.main()
