import unittest

from scripts.build_p0_eft_janus_cpt_pt_state_law_gate import build_payload


class JanusCPTPTStateLawTests(unittest.TestCase):
    def test_cpt_state_principle_is_real_but_alpha_not_closed(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["closed_by_bibliography"]["pt_cpt_can_select_preferred_vacuum"])
        self.assertFalse(payload["not_closed_for_janus"]["alpha_from_state_no_fit"])
        self.assertFalse(payload["no_fit_alpha_generated"])

    def test_required_derivation_targets_state_energy(self):
        payload = build_payload()
        required = " ".join(payload["required_derivation"])

        self.assertIn("vacuum energy", required)
        self.assertIn("M_bridge/alpha", required)


if __name__ == "__main__":
    unittest.main()
