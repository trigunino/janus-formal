from __future__ import annotations

import unittest

from scripts.build_p0_local_phi_scouple_symbolic_restricted_audit import build_payload


class P0LocalPhiScoupleSymbolicRestrictedAuditTests(unittest.TestCase):
    def test_symbolic_audit_confirms_family_not_no_go(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "restricted-symbolic-family-obstruction-confirmed")
        self.assertTrue(payload["nonunique_candidates_exist"])
        self.assertFalse(payload["no_go_proved"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_candidates_share_same_weak_linear_limit(self) -> None:
        rows = build_payload()["same_linear_limit_candidates"]

        self.assertGreaterEqual(len(rows), 3)
        self.assertTrue(all(row["same_linear_limit_as_linear"] for row in rows))
        self.assertTrue(all(row["weak_surface_value"] == "I_matter*c1" for row in rows))

    def test_assumptions_do_not_include_split_noether(self) -> None:
        payload = build_payload()
        assumptions = " ".join(payload["assumptions"])
        reason = payload["reason_no_go_not_proved"]

        self.assertIn("no split Noether", assumptions)
        self.assertIn("Split Noether", reason)

    def test_model_noether_constraints_reduce_only_if_imposed(self) -> None:
        payload = build_payload()
        constraints = " ".join(row["constraint"] + row["solves"] for row in payload["noether_model_constraints"])

        self.assertTrue(payload["noether_reduced_unique_if_imposed"])
        self.assertFalse(payload["noether_constraints_source_derived"])
        self.assertTrue(payload["split_noether_calculable_target_available"])
        self.assertIn("dPhi/dI_metric", constraints)
        self.assertIn("c3", constraints)
        self.assertIn("c2", constraints)


if __name__ == "__main__":
    unittest.main()
