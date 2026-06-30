from __future__ import annotations

import unittest

from scripts.build_p0_noncomoving_momentum_t0i_closure_target import build_payload


class P0NoncomovingMomentumT0iClosureTargetTests(unittest.TestCase):
    def test_target_is_open_not_predictive(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertEqual(payload["status"], "momentum-closure-target-open")
        self.assertTrue(decision["t0i_formula_target_defined"])
        self.assertTrue(decision["dust_limit_checked"])
        self.assertFalse(decision["pressure_pi_momentum_transport_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_formulas_cover_perfect_fluid_dust_and_comoving_limits(self) -> None:
        formulas = " ".join(build_payload()["formulas"].values())

        self.assertIn("(rho+p) gamma^2 beta_i", formulas)
        self.assertIn("Pi0i", formulas)
        self.assertIn("rho gamma^2 beta_i", formulas)
        self.assertIn("T0i=0", formulas)

    def test_requirements_keep_momentum_and_scalar_factors_separate(self) -> None:
        requirements = " ".join(build_payload()["requirements"])

        self.assertIn("beta_i", requirements)
        self.assertIn("p_cross", requirements)
        self.assertIn("Pi0i/Pi00", requirements)
        self.assertIn("R_plus/R_minus", requirements)
        self.assertIn("separate from scalar Q_det/Q_cross", requirements)


if __name__ == "__main__":
    unittest.main()
