import unittest

from scripts.build_p0_eft_janus_chi_ll_selection_reprise_gate import build_payload


class JanusChiLLSelectionRepriseTests(unittest.TestCase):
    def test_reprise_identifies_existing_work_and_remaining_blocker(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["already_done"]["mass_radius_relation_derived"])
        self.assertTrue(payload["already_done"]["discrete_sector_family_ready"])
        self.assertTrue(payload["already_done"]["primitive_flux_standard_no_go"])
        self.assertFalse(payload["chi_LL_selected_no_fit"])

    def test_best_next_target_is_pt_boundary_state(self):
        payload = build_payload()

        self.assertEqual(payload["best_next_target"], "PT_boundary_state_selects_chi")
        self.assertIn("do not redo primitive flux no-go", payload["avoid_duplication"])


if __name__ == "__main__":
    unittest.main()
