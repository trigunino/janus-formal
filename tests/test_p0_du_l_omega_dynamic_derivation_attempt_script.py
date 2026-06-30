from __future__ import annotations

import unittest

from scripts.build_p0_du_l_omega_dynamic_derivation_attempt import build_payload


class P0DULOmegaDynamicDerivationAttemptTests(unittest.TestCase):
    def test_attempt_is_bounded_open_and_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dynamic-du-l-omega-derivation-attempt-open")
        self.assertTrue(payload["l_as_lorentz_tetrad_bridge"])
        self.assertTrue(payload["omega_defined_from_l"])
        self.assertTrue(payload["omega_u_u_zero_cancellation_proved_algebraically"])
        self.assertTrue(payload["projected_cuu_cancellation_target_defined"])
        self.assertFalse(payload["projected_cuu_cancellation_source_derived"])
        self.assertFalse(payload["source_action_law_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_derivation_records_l_omega_dust_and_cuu_target(self) -> None:
        text = " ".join(
            row["statement"] + row["formula"] + row["proved"]
            for row in build_payload()["derivation_steps"]
        )

        self.assertIn("L maps source-sector tetrad", text)
        self.assertIn("Omega_alpha=(D_alpha L)L^{-1}", text)
        self.assertIn("Omega_u u=0", text)
        self.assertIn("projected Cuu", text)
        self.assertIn("target-not-source-derived", text)

    def test_algebraic_vs_source_dependent_status_is_explicit(self) -> None:
        payload = build_payload()
        algebra = " ".join(payload["algebraic_results"])
        gaps = " ".join(payload["source_dependent_gaps"])

        self.assertIn("eta-antisymmetric", algebra)
        self.assertIn("rank-one dust Omega residual", algebra)
        self.assertIn("projected Cuu row", algebra)
        self.assertIn("not selected the dynamic L", gaps)
        self.assertIn("not derived", gaps)
        self.assertIn("not proved from the action", gaps)

    def test_same_l_required_and_shortcuts_forbidden(self) -> None:
        payload = build_payload()
        requirements = {row["requirement"]: row for row in payload["consistency_requirements"]}
        details = " ".join(row["detail"] for row in payload["consistency_requirements"])

        self.assertTrue(payload["same_l_for_k_qcross_required"])
        self.assertFalse(payload["fitting_allowed"])
        self.assertFalse(payload["scalar_absorption_allowed"])
        self.assertFalse(requirements["same_l_for_k"]["closed"])
        self.assertFalse(requirements["same_l_for_qcross"]["closed"])
        self.assertTrue(requirements["no_scalar_absorption"]["closed"])
        self.assertTrue(requirements["no_posthoc_fit"]["closed"])
        self.assertIn("K_plus/K_minus", details)
        self.assertIn("Q_cross", details)
        self.assertIn("fitted scalar", details)


if __name__ == "__main__":
    unittest.main()
