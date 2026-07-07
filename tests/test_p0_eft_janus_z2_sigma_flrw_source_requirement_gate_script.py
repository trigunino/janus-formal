import unittest

from scripts.build_p0_eft_janus_z2_sigma_flrw_source_requirement_gate import build_payload


class SigmaFLRWSourceRequirementGateTests(unittest.TestCase):
    def test_archives_paper_vs_sigma_level_separation(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["archived_result"]["not_a_contradiction"])
        self.assertTrue(payload["archived_result"]["published_janus_uses_global_bimetric_bulk_source"])
        self.assertTrue(payload["archived_result"]["sigma_only_variation_emits_zero_source"])

    def test_current_action_still_has_no_flrw_source(self):
        payload = build_payload()

        self.assertEqual(payload["current_action_status"]["emitting_admitted_terms"], [])
        self.assertFalse(payload["current_action_status"]["E_Z2Sigma_a2_ready"])

    def test_preferred_next_route_is_bulk_bimetric_source(self):
        payload = build_payload()

        routes = payload["what_the_action_needs_for_FLRW"]
        self.assertTrue(routes["bulk_bimetric_stress"]["preferred_next_route"])
        self.assertFalse(routes["bulk_bimetric_stress"]["ready"])
        self.assertTrue(payload["decision"]["continue_current_branch_by_formalizing_bulk_bimetric_FLRW_source"])


if __name__ == "__main__":
    unittest.main()
