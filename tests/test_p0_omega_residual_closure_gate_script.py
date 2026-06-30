from __future__ import annotations

import unittest

from scripts.build_p0_omega_residual_closure_gate import build_payload


class P0OmegaResidualClosureGateTests(unittest.TestCase):
    def test_omega_gate_is_open_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "omega-residual-gate-open")
        self.assertTrue(payload["omega_residual_isolated"])
        self.assertTrue(payload["omega_dust_rank_one_condition_available"])
        self.assertFalse(payload["dust_rank_one_condition_closed"])
        self.assertFalse(payload["k_qcross_same_omega_closed"])
        self.assertTrue(payload["omega_k_qcross_consistency_gate_available"])
        self.assertTrue(payload["omega_closure_routes_gate_available"])
        self.assertFalse(payload["mirror_inverse_closed"])
        self.assertTrue(payload["no_fit_selection_rule_closed"])
        self.assertFalse(payload["omega_residual_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_gates_cover_rank_one_k_qcross_mirror_and_no_fit(self) -> None:
        text = " ".join(row["gate"] + row["requirement"] for row in build_payload()["gate_rows"])

        self.assertIn("Omega^T T_minus + T_minus Omega", text)
        self.assertIn("T_minus=rho u u", text)
        self.assertIn("K transport and Q_cross", text)
        self.assertIn("mirror", text)
        self.assertIn("cannot be chosen only to cancel", text)


if __name__ == "__main__":
    unittest.main()
