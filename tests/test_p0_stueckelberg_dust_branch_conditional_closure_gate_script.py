from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_dust_branch_conditional_closure_gate import build_payload


class P0DustBranchConditionalClosureGateTests(unittest.TestCase):
    def test_dust_branch_is_diagnostic_not_prediction(self) -> None:
        payload = build_payload()
        verdict = payload["verdict"]

        self.assertEqual(verdict["dust_branch_status"], "conditionally-fermable-not-closed")
        self.assertTrue(verdict["can_advance_to_numerical_diagnostic"])
        self.assertFalse(verdict["can_claim_physical_prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_all_required_gates_are_listed(self) -> None:
        payload = build_payload()
        names = {row["name"] for row in payload["gates"]}

        self.assertIn("projected_dust_variation_identity", names)
        self.assertIn("phi_l_convention_lock", names)
        self.assertIn("density_volume_consistency", names)
        self.assertIn("mirror_inverse_residual", names)
        self.assertIn("integrability_curls", names)

    def test_open_gates_prevent_physical_closure(self) -> None:
        payload = build_payload()
        statuses = " ".join(row["status"] for row in payload["gates"])

        self.assertIn("open", statuses)
        self.assertIn("required-not-proved", statuses)
        self.assertFalse(payload["physics_closed"])


if __name__ == "__main__":
    unittest.main()
