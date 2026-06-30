from __future__ import annotations

import unittest

from scripts.build_p0_omega_dust_rank_one_condition import build_payload


class P0OmegaDustRankOneConditionTests(unittest.TestCase):
    def test_rank_one_gate_is_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "rank-one-condition-fails-prediction")
        self.assertTrue(payload["rank_one_substitution_done"])
        self.assertFalse(payload["fit_choice_allowed"])
        self.assertTrue(payload["shared_with_k_qcross_required"])
        self.assertFalse(payload["residual_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["prediction_claim"])

    def test_zero_condition_distinguishes_parallel_from_orthogonal(self) -> None:
        payload = build_payload()
        algebra = " ".join(payload["algebra"].values())

        self.assertTrue(payload["omega_u_parallel_required"])
        self.assertTrue(payload["lorentz_orthogonal_only_insufficient"])
        self.assertTrue(payload["timelike_parallel_forces_omega_u_zero"])
        self.assertIn("Omega u parallel u", algebra)
        self.assertIn("Omega u perpendicular u", algebra)
        self.assertIn("Omega u=0", algebra)
        self.assertIn("not sufficient", algebra)

    def test_condition_must_be_shared_with_k_and_qcross(self) -> None:
        requirements = " ".join(build_payload()["closure_requirements"])

        self.assertIn("same L", requirements)
        self.assertIn("K_plus/K_minus", requirements)
        self.assertIn("Q_cross", requirements)
        self.assertIn("no post-hoc fit", requirements)
        self.assertIn("source-derived transport", requirements)

    def test_blocked_shortcuts_forbid_fit_and_scalar_absorption(self) -> None:
        shortcuts = " ".join(build_payload()["blocked_shortcuts"])

        self.assertIn("Lorentz orthogonality", shortcuts)
        self.assertIn("scalar density", shortcuts)
        self.assertIn("scalar Q_cross", shortcuts)
        self.assertIn("survey fit", shortcuts)
        self.assertIn("another for optical Q_cross", shortcuts)


if __name__ == "__main__":
    unittest.main()
