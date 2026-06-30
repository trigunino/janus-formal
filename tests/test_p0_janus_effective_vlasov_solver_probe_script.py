from __future__ import annotations

import unittest

from scripts.build_p0_janus_effective_vlasov_solver_probe import build_payload, render_markdown


class P0JanusEffectiveVlasovSolverProbeScriptTests(unittest.TestCase):
    def test_probe_is_diagnostic_and_conserves_mass(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["diagnostic_only"])
        self.assertTrue(payload["uses_toy_force"])
        self.assertFalse(payload["uses_source_derived_janus_force"])
        self.assertLess(payload["metrics"]["mass_abs_error"], 1e-12)
        self.assertGreaterEqual(payload["metrics"]["min_f_final"], 0.0)

    def test_moment_fields_include_pressure_and_heat_flux(self) -> None:
        fields = build_payload()["moment_fields"]

        self.assertIn("rho", fields)
        self.assertIn("P", fields)
        self.assertIn("Pi", fields)
        self.assertIn("Q", fields)

    def test_no_physics_or_prediction_claim(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_boundary(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Diagnostic only: True", markdown)
        self.assertIn("not a prediction layer", markdown)


if __name__ == "__main__":
    unittest.main()
