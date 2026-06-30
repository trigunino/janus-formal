from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_p0_janus_weakfield_lgeom_lorentz_no_go_gate import (
    build_payload,
    linear_lorentz_residual,
    render_markdown,
    weakfield_lgeom,
)


class P0JanusWeakfieldLgeomLorentzNoGoGateTests(unittest.TestCase):
    def test_lgeom_linear_diagonal_matches_relative_potentials(self) -> None:
        delta_phi, delta_psi = sp.symbols("Delta_Phi Delta_Psi")
        lgeom = weakfield_lgeom()

        self.assertEqual(lgeom[0, 0], 1 - delta_phi)
        self.assertEqual(lgeom[1, 1], 1 + delta_psi)

    def test_lorentz_residual_forces_zero_relative_potentials(self) -> None:
        delta_phi, delta_psi = sp.symbols("Delta_Phi Delta_Psi")
        residual = linear_lorentz_residual()

        self.assertEqual(residual[0, 0], 2 * delta_phi)
        self.assertEqual(residual[1, 1], 2 * delta_psi)
        self.assertEqual(residual.subs({delta_phi: 0, delta_psi: 0}), sp.zeros(4))

    def test_payload_rejects_generic_and_dust_slip_lgeom(self) -> None:
        payload = build_payload()
        rows = {row["case"]: row for row in payload["no_go_rows"]}

        self.assertFalse(rows["generic weak-field relative potentials"]["lgeom_admissible"])
        self.assertFalse(rows["dust/slip but nonzero relative potential"]["lgeom_admissible"])
        self.assertTrue(rows["identical local potentials"]["lgeom_admissible"])
        self.assertTrue(payload["lgeom_generic_branch_rejected"])

    def test_same_l_remains_open_without_source_transport(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["source_selected_perturbed_l_found"])
        self.assertFalse(payload["same_l_global_perturbed_branch_selected"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_lists_forbidden_scalar_absorption(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("absorb the Lorentz residual into Q_det or Q_cross", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
