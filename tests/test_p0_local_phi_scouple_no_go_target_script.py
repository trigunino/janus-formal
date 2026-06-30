from __future__ import annotations

import unittest

from scripts.build_p0_local_phi_scouple_no_go_target import build_payload


class P0LocalPhiScoupleNoGoTargetTests(unittest.TestCase):
    def test_target_is_not_proved_or_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "target-not-proved")
        self.assertEqual(payload["bounded_scope"], "local-low-derivative-only")
        self.assertFalse(payload["theorem_proved"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_assumptions_cover_requested_classification(self) -> None:
        assumptions = {row["assumption"]: row["classification"] for row in build_payload()["assumptions"]}

        self.assertEqual(assumptions["locality"], "scope restriction")
        self.assertEqual(assumptions["low_derivative"], "scope restriction")
        self.assertEqual(assumptions["mirror_symmetry"], "structural symmetry")
        self.assertEqual(assumptions["M15_B_4vol"], "source-measure anchor")
        self.assertEqual(assumptions["same_L_for_K_and_Qcross"], "transport coherence")
        self.assertEqual(assumptions["weak_field_sign"], "linear-limit filter")
        self.assertEqual(assumptions["split_Noether_R_plus_R_minus"], "closure test")

    def test_if_proved_eliminates_rustine_and_family_obstruction(self) -> None:
        payload = build_payload()
        elimination = " ".join(payload["if_proved_eliminates"])

        self.assertTrue(payload["rustine_eliminated_if_proved"])
        self.assertTrue(payload["family_obstruction_eliminated_if_proved"])
        self.assertIn("rustine", elimination)
        self.assertIn("family obstruction", elimination)
        self.assertIn("new axiom", elimination)

    def test_remaining_family_risks_are_explicit(self) -> None:
        payload = build_payload()
        risks = " ".join(payload["remaining_family_risks"])

        self.assertTrue(payload["remaining_family_possible"])
        self.assertTrue(payload["restricted_symbolic_audit_available"])
        self.assertIn("higher-derivative", risks)
        self.assertIn("nonlocal", risks)
        self.assertIn("mirror-symmetric", risks)
        self.assertIn("new source axioms", risks)


if __name__ == "__main__":
    unittest.main()
