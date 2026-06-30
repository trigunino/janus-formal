from __future__ import annotations

import unittest

from scripts.build_p0_pulled_dust_el_cuu_substitution_proof import build_payload


class P0PulledDustELCuuSubstitutionProofTests(unittest.TestCase):
    def test_proof_state_is_open_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "substitution-proof-open")
        self.assertEqual(payload["particle_action_cuu_derivation_status"], "pulled-particle-action-cuu-derivation-partial")
        self.assertTrue(payload["particle_geodesic_variation_closed"])
        self.assertTrue(payload["cold_dust_lift_closed"])
        self.assertTrue(payload["cross_pullback_closed"])
        self.assertTrue(payload["standard_projection_closed"])
        self.assertTrue(payload["single_cross_dust_rows_closed"])
        self.assertTrue(payload["mirror_inverse_closed"])
        self.assertFalse(payload["dynamic_phi_l_selection_closed"])
        self.assertTrue(payload["phi_scouple_source_or_axiom_decision_available"])
        self.assertFalse(payload["all_rows_closed"])
        self.assertFalse(payload["projected_cuu_identity_proved"])
        self.assertFalse(payload["prediction_ready"])

    def test_proof_rows_include_four_required_substitutions_and_mirror(self) -> None:
        rows = {row["row"]: row for row in build_payload()["proof_rows"]}

        self.assertIn("projected_dust_variation", rows)
        self.assertIn("dphi_density_measure", rows)
        self.assertIn("dl_velocity_tetrad", rows)
        self.assertIn("connection_force", rows)
        self.assertIn("mirror_inverse", rows)
        self.assertIn("dynamic_phi_l_selection", rows)
        self.assertEqual(rows["projected_dust_variation"]["status"], "standard-closed")
        self.assertEqual(rows["dphi_density_measure"]["status"], "closed-for-single-cross-dust")
        self.assertEqual(rows["connection_force"]["status"], "closed-for-single-cross-dust")
        self.assertEqual(rows["mirror_inverse"]["status"], "closed-if-inverse-constraint-in-action")

    def test_conclusion_names_target_formula_but_not_proved(self) -> None:
        conclusion = build_payload()["conclusion"]

        self.assertEqual(conclusion["formula"], "h E_phi/E_L = rho h C(u_to,u_to)")
        self.assertFalse(conclusion["proved"])
        self.assertTrue(conclusion["conditional_progress"])

    def test_closure_needed_keeps_measure_falpha_mirror_and_pressure_explicit(self) -> None:
        needed = " ".join(build_payload()["closure_needed"])

        self.assertIn("dynamic phi/L", needed)
        self.assertIn("sign convention", needed)
        self.assertIn("pressure/Pi", needed)


if __name__ == "__main__":
    unittest.main()
