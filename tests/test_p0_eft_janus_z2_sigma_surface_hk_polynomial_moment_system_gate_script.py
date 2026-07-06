from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_surface_hk_polynomial_moment_system_gate import (
    build_payload,
    render_markdown,
)


class SurfaceHKPolynomialMomentSystemGateTests(unittest.TestCase):
    def test_bending_moment_components_are_derived(self) -> None:
        payload = build_payload()
        moment = payload["bending_moment"]

        self.assertTrue(payload["alpha_K_polynomial_moment_formula_ready"])
        self.assertEqual(moment["D_ab"], "a1*h_ab + 2*a2*K*h_ab + 2*a3*K_ab")
        self.assertEqual(moment["D_tau"], "-a1 - 2*a2*K + 2*a3*K_tau")
        self.assertEqual(moment["D_s"], "a1 + 2*a2*K + 2*a3*K_s")
        self.assertIn("3*D_s*dR_K_s", moment["alpha_K_radial"])

    def test_metric_stress_formula_ready_but_coefficients_remain_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["alpha_h_surface_stress_formula_ready"])
        self.assertFalse(payload["active_Janus_coefficients_derived"])
        self.assertFalse(payload["coefficient_system"]["metric_stress_equations_available"])
        self.assertTrue(payload["coefficient_system"]["a0_requires_metric_or_reference_energy_condition"])

    def test_markdown_reports_bending_moment(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Bending Moment", markdown)
        self.assertIn("alpha_K_radial", markdown)


if __name__ == "__main__":
    unittest.main()
