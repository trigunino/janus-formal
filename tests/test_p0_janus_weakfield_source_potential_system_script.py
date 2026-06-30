from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_p0_janus_weakfield_source_potential_system import (
    b4vol_linearized,
    build_payload,
    determinant_log_density_factor,
    render_markdown,
)


class P0JanusWeakfieldSourcePotentialSystemTests(unittest.TestCase):
    def test_linearized_determinant_ratio_keeps_four_volume_terms(self) -> None:
        phi_plus, phi_minus, psi_plus, psi_minus = sp.symbols("Phi_plus Phi_minus Psi_plus Psi_minus")

        self.assertEqual(determinant_log_density_factor(phi_plus, psi_plus), phi_plus - 3 * psi_plus)
        self.assertEqual(
            sp.simplify(b4vol_linearized(phi_minus, psi_minus, phi_plus, psi_plus) - 1),
            phi_minus - phi_plus - 3 * psi_minus + 3 * psi_plus,
        )

    def test_poisson_rows_preserve_janus_cross_source_slots(self) -> None:
        payload = build_payload()
        rows = " ".join(row["row"] + " " + row["source_slot"] for row in payload["poisson_rows"])

        self.assertIn("B_4vol_plus_from_minus rho_minus_to_plus", rows)
        self.assertIn("B_4vol_minus_from_plus rho_plus_to_minus", rows)
        self.assertIn("G_plus = chi", rows)
        self.assertIn("G_minus = -chi", rows)
        self.assertTrue(payload["janus_cross_source_slots_preserved"])

    def test_slip_and_dust_limits_are_explicit_but_not_general_closure(self) -> None:
        payload = build_payload()
        slip = " ".join(row["row"] + " " + row["dust_limit"] for row in payload["slip_rows"])

        self.assertIn("Pi_plus_effective_ij", slip)
        self.assertIn("Pi_minus_effective_ij", slip)
        self.assertIn("dust", slip)
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_payload_forbids_fit_and_scalar_absorption(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "weakfield-source-potential-system-open")
        self.assertTrue(payload["linearized_determinant_density_ratio_derived"])
        self.assertTrue(payload["determinant_not_lensing_amplitude"])
        self.assertTrue(payload["qdet_qcross_absorption_forbidden"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["janus_source_potentials_solved"])
        self.assertFalse(payload["boundary_conditions_source_derived"])

    def test_markdown_reports_open_rows(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("# P0 Janus Weak-Field Source Potential System", markdown)
        self.assertIn("sqrt(-g) linearized", markdown)
        self.assertIn("Janus source potentials solved: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
