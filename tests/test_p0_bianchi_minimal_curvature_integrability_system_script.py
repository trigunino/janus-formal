from __future__ import annotations

import unittest

from scripts.build_p0_bianchi_minimal_curvature_integrability_system import build_payload


class P0BianchiMinimalCurvatureIntegrabilitySystemTests(unittest.TestCase):
    def test_system_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "curvature-integrability-system-open")
        self.assertTrue(payload["spin_connection_identity_algebra_closed"])
        self.assertTrue(payload["curvature_commutator_identity_closed"])
        self.assertTrue(payload["relative_curvature_formula_closed"])
        self.assertTrue(payload["flow_boost_constraint_closed"])
        self.assertFalse(payload["curvature_match_closed"])
        self.assertFalse(payload["mirror_curvature_closed"])
        self.assertTrue(payload["transverse_unknowns_remain"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_unknowns_are_transverse_not_fitted(self) -> None:
        unknowns = {row["symbol"]: row for row in build_payload()["unknowns"]}

        self.assertIn("A_perp_i", unknowns)
        self.assertIn("R_alpha", unknowns)
        self.assertIn("F_relative_alpha_beta", unknowns)
        self.assertFalse(unknowns["A_perp_i"]["selected"])
        self.assertFalse(unknowns["R_alpha"]["selected"])
        self.assertEqual(unknowns["F_relative_alpha_beta"]["selected"], "source-computable")
        self.assertIn("R_s - L R_o L^{-1}", unknowns["F_relative_alpha_beta"]["meaning"])

    def test_equations_include_curvature_and_mirror(self) -> None:
        equations = " ".join(row["equation"] for row in build_payload()["reduced_equations"])

        self.assertIn("u^alpha A_alpha=a_req", equations)
        self.assertIn("[D_alpha,D_beta]L=R_s,alpha_beta L - L R_o,alpha_beta", equations)
        self.assertIn("F_relative_alpha_beta=R_s,alpha_beta - L R_o,alpha_beta L^{-1}", equations)
        self.assertIn("D_[alpha Omega_beta]+[Omega_alpha,Omega_beta]", equations)
        self.assertIn("F_relative_alpha_beta", equations)
        self.assertIn("R_alpha_AB u^B=0", equations)
        self.assertIn("inverse-pushforward", equations)

    def test_outcomes_do_not_unlock_prediction(self) -> None:
        outcomes = {row["case"]: row for row in build_payload()["outcomes"]}

        self.assertFalse(outcomes["pde_has_solution"]["prediction_ready"])
        self.assertFalse(outcomes["pde_no_solution"]["prediction_ready"])
        self.assertIn("same-L Q_cross", outcomes["pde_has_solution"]["remaining"])
        self.assertIn("reject branch", outcomes["pde_no_solution"]["remaining"])


if __name__ == "__main__":
    unittest.main()
