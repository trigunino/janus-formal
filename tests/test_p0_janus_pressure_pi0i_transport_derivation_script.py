from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_p0_janus_pressure_pi0i_transport_derivation import (
    build_payload,
    linear_pi0i_from_boost,
    linear_t0i_momentum,
    render_markdown,
)


class P0JanusPressurePi0iTransportDerivationTests(unittest.TestCase):
    def test_linear_pi0i_from_boosted_spatial_pi(self) -> None:
        bx, by, bz = sp.symbols("beta_x beta_y beta_z")
        pxx, pxy, pxz = sp.symbols("Pi_xx Pi_xy Pi_xz")
        pi = linear_pi0i_from_boost()

        self.assertEqual(pi["Pi0x"], bx * pxx + by * pxy + bz * pxz)

    def test_linear_t0i_contains_enthalpy_and_pi_terms(self) -> None:
        rho, pressure, bx = sp.symbols("rho p beta_x")
        t0i = linear_t0i_momentum()

        self.assertIn((rho + pressure) * bx, sp.Add.make_args(t0i["T0x"]))
        self.assertIn("Pi_xx", sp.sstr(t0i["T0x"]))

    def test_payload_closes_algebraic_transport_only(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "pressure-pi0i-transport-derived-source-open")
        self.assertTrue(payload["same_l_transport_formula_derived"])
        self.assertTrue(payload["pressure_t0i_formula_derived"])
        self.assertTrue(payload["pi0i_boost_formula_derived"])
        self.assertTrue(payload["perfect_fluid_transport_closed_algebraically"])
        self.assertTrue(payload["anisotropic_pi0i_transport_closed_algebraically"])
        self.assertFalse(payload["equation_of_state_source_derived"])
        self.assertFalse(payload["pi_evolution_source_derived"])
        self.assertFalse(payload["source_derived_beta_available"])
        self.assertFalse(payload["residuals_closed"])

    def test_no_fit_or_prediction_claim(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_source_dependent_remainders(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Equation of state source-derived: False", markdown)
        self.assertIn("Pi evolution source-derived: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
