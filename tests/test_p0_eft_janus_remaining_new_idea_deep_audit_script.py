import unittest

from scripts.build_p0_eft_janus_remaining_new_idea_deep_audit_gate import build_payload


class JanusRemainingNewIdeaDeepAuditTests(unittest.TestCase):
    def test_remaining_routes_are_audited_without_alpha_closure(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["all_remaining_routes_audited"])
        self.assertFalse(payload["any_remaining_route_closes_alpha_now"])
        self.assertEqual(len(payload["routes"]), 5)

    def test_best_survivors_are_prioritized(self):
        payload = build_payload()

        self.assertEqual(payload["best_survivors_after_deep_audit"][0], "lightlike_brane_bridge_source")
        self.assertIn("unimodular_four_form_sector_constant", payload["best_survivors_after_deep_audit"])


if __name__ == "__main__":
    unittest.main()
