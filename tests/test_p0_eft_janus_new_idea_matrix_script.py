import unittest

from scripts.build_p0_eft_janus_new_idea_matrix_gate import build_payload


class JanusNewIdeaMatrixTests(unittest.TestCase):
    def test_all_ideas_are_ranked_and_blocked_explicitly(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["bibliography_checked"])
        self.assertTrue(payload["all_ideas_have_explicit_blocker"])
        self.assertFalse(payload["no_fit_alpha_generated_now"])
        self.assertEqual(payload["ideas"][0]["id"], "unimodular_four_form_sector_constant")

    def test_no_magic_fit_policy_is_visible(self):
        payload = build_payload()

        self.assertTrue(payload["no_magic_fit_allowed"])
        self.assertIn("state law", payload["verdict"])
        self.assertIn("unimodular_four_form_sector_constant", payload["recommended_next_if_new_physics_allowed"])


if __name__ == "__main__":
    unittest.main()
