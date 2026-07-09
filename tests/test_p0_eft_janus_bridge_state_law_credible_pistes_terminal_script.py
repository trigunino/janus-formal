import unittest

from scripts.build_p0_eft_janus_bridge_state_law_credible_pistes_terminal_gate import (
    build_payload,
)


class JanusAlphaBridgeStateLawCrediblePistesTerminalTests(unittest.TestCase):
    def test_terminal_verdict_blocks_no_fit_without_boundary_state_law(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["explicit_boundary_state_law_derived"])
        self.assertTrue(payload["rules"]["no_direct_alpha_fit"])
        self.assertTrue(payload["rules"]["observation_selection_is_not_no_fit"])

    def test_three_remaining_pistes_are_classified(self):
        payload = build_payload()
        statuses = {row["id"]: row["status"] for row in payload["pistes"]}

        self.assertEqual(statuses["composite_boundary_state_law"], "credible_but_not_closed")
        self.assertEqual(statuses["alpha_superselection_sector"], "viable_non_no_fit_contract")
        self.assertEqual(statuses["paper_reference_gap_report"], "useful_formal_output")


if __name__ == "__main__":
    unittest.main()
