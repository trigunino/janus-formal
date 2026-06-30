from __future__ import annotations

import unittest

from scripts.build_p0_scouple_matter_invariant_solver import build_payload, render_markdown


class P0ScoupleMatterInvariantSolverTests(unittest.TestCase):
    def test_dust_coefficient_fixed_but_matter_family_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "matter-invariant-family-open")
        self.assertEqual(payload["cold_vlasov_probe_status"], "cold-vlasov-dust-preservation-conditional")
        self.assertTrue(payload["dust_branch_closed_conditionally"])
        self.assertFalse(payload["general_dust_closure_proved"])
        self.assertTrue(payload["dust_coefficient_fixed"])
        self.assertFalse(payload["pressure_coefficient_source_fixed"])
        self.assertFalse(payload["pi_coefficient_source_fixed"])
        self.assertFalse(payload["matter_family_unique"])
        self.assertFalse(payload["prediction_ready"])

    def test_pressure_and_pi_require_tensor_laws(self) -> None:
        terms = {row["term"]: row for row in build_payload()["tensor_terms"]}

        self.assertFalse(terms["p"]["dust_fixed"])
        self.assertTrue(terms["p"]["requires_tensor_law"])
        self.assertFalse(terms["Pi"]["dust_fixed"])
        self.assertTrue(terms["Pi"]["requires_tensor_law"])

    def test_closure_checks_forbid_scalar_absorption(self) -> None:
        payload = build_payload()
        checks = {row["check"]: row for row in payload["closure_checks"]}

        self.assertTrue(checks["dust_limit"]["closed"])
        self.assertFalse(checks["perfect_fluid"]["closed"])
        self.assertFalse(checks["anisotropic_stress"]["closed"])
        self.assertFalse(checks["scalar_absorption"]["closed"])
        self.assertFalse(payload["scalar_q_absorption_allowed"])
        self.assertTrue(payload["multistream_generates_pressure"])
        self.assertTrue(payload["multistream_generates_pi"])

    def test_symbolic_solutions_show_missing_eos_and_pi_law(self) -> None:
        solutions = build_payload()["scalar_absorption_solutions"]

        self.assertIn("a", solutions["dust"])
        self.assertIn("b: 0", solutions["perfect_fluid_without_eos"])
        self.assertIn("c", solutions["anisotropic_without_pi_law"])

    def test_markdown_keeps_eos_pi_requirements_visible(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("EOS required: True", markdown)
        self.assertIn("Dust branch closed conditionally: True", markdown)
        self.assertIn("General dust closure proved: False", markdown)
        self.assertIn("Pi transport required: True", markdown)
        self.assertIn("Scalar Q absorption allowed: False", markdown)


if __name__ == "__main__":
    unittest.main()
