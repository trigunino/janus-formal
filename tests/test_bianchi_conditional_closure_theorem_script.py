from __future__ import annotations

import unittest

from scripts.build_bianchi_conditional_closure_theorem import build_payload


class BianchiConditionalClosureTheoremTests(unittest.TestCase):
    def test_conditional_implication_is_closed_but_not_source_derived(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["conditional_closure_proved"])
        self.assertFalse(payload["conditions_source_derived"])
        self.assertFalse(payload["residuals_physically_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_positive_and_negative_chains_end_in_zero_residuals(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["positive_chain"][-1], "therefore R_plus^mu=0")
        self.assertEqual(payload["negative_chain"][-1], "therefore R_minus^mu=0")

    def test_theorem_mentions_all_required_assumptions(self) -> None:
        claim = build_payload()["theorem"]["claim"]

        self.assertIn("same-sector dust stresses are conserved", claim)
        self.assertIn("transported continuities", claim)
        self.assertIn("transported force equations", claim)
        self.assertIn("connection-difference", claim)

    def test_remaining_work_keeps_l_and_qcross_compatibility_open(self) -> None:
        remaining = " ".join(build_payload()["remaining_physical_work"])

        self.assertIn("L_minus_to_plus", remaining)
        self.assertIn("Q_cross", remaining)
        self.assertIn("K_plus/K_minus", remaining)


if __name__ == "__main__":
    unittest.main()
