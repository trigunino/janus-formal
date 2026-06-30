from __future__ import annotations

import unittest

from scripts.build_p0_pulled_m_symmetric_l_substitution import build_payload


class P0PulledMSymmetricLSubstitutionTests(unittest.TestCase):
    def test_symmetric_piece_substituted_but_omega_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "symmetric-l-substitution-closed-omega-open")
        self.assertTrue(payload["symmetric_l_piece_substituted"])
        self.assertTrue(payload["m_variation_split_closed"])
        self.assertTrue(payload["omega_residual_isolated"])
        self.assertFalse(payload["omega_residual_closed"])
        self.assertTrue(payload["dust_rank_one_omega_condition_available"])
        self.assertTrue(payload["same_omega_for_k_qcross_required"])
        self.assertTrue(payload["omega_residual_closure_gate_available"])
        self.assertFalse(payload["pulled_m_metric_response_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_omega_residual_and_k_qcross_guard(self) -> None:
        text = " ".join(row["formula"] + row["status"] for row in build_payload()["substitution_rows"])

        self.assertIn("S_g + Omega", text)
        self.assertIn("delta_g M[S_g]", text)
        self.assertIn("Omega^T T_minus + T_minus Omega", text)
        self.assertIn("T_minus=rho uu", text)
        self.assertIn("K transport and Q_cross", text)


if __name__ == "__main__":
    unittest.main()
