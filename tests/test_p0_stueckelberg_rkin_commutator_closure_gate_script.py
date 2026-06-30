from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_rkin_commutator_closure_gate import build_payload


class P0RkinCommutatorClosureGateTests(unittest.TestCase):
    def test_rkin_not_zero_generically(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertFalse(decision["rkin_zero_generically"])
        self.assertTrue(decision["rkin_zero_on_cold_support_possible"])
        self.assertFalse(decision["full_phase_space_closure"])
        self.assertFalse(payload["prediction_ready"])

    def test_closure_cases_distinguish_full_cold_and_generic(self) -> None:
        payload = build_payload()
        cases = {row["case"]: row for row in payload["closure_cases"]}

        self.assertEqual(cases["full_phase_space_symplectomorphism"]["rkin"], "0")
        self.assertEqual(cases["dust_cold_shell"]["rkin"], "zero-on-support")
        self.assertEqual(cases["generic_kinetic"]["rkin"], "nonzero")

    def test_required_proofs_include_phase_space_and_no_absorption(self) -> None:
        payload = build_payload()
        proofs = " ".join(payload["required_proofs"])

        self.assertIn("mass shell", proofs)
        self.assertIn("phase-space support", proofs)
        self.assertIn("Q_cross or Q_det", proofs)


if __name__ == "__main__":
    unittest.main()
