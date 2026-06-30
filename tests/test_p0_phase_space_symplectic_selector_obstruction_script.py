from __future__ import annotations

import unittest

from scripts.build_p0_phase_space_symplectic_selector_obstruction import (
    build_payload,
    render_markdown,
)


class P0PhaseSpaceSymplecticSelectorObstructionTests(unittest.TestCase):
    def test_canonical_family_preserves_phase_space_det(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["canonical_liouville_det_equals_one"])
        self.assertTrue(payload["arbitrary_positive_a_allowed"])
        self.assertTrue(payload["projected_j_phi_values_distinct"])
        self.assertTrue(all(row["phase_space_determinant"] == 1.0 for row in payload["family"]))
        self.assertGreater(len({row["projected_j_phi_candidate"] for row in payload["family"]}), 1)

    def test_phase_space_route_does_not_select_phi_j_l(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "phase-space-symplectic-selector-obstruction-open")
        self.assertFalse(payload["phase_space_route_selects_j_phi"])
        self.assertFalse(payload["phase_space_route_closes_phi_j_l"])
        self.assertTrue(payload["requires_hamiltonian_or_source_branch"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_zero_rustine_guards_are_closed(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["observational_fit_forbidden"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertTrue(payload["qdet_qcross_absorption_forbidden"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertTrue(payload["hidden_axiom_forbidden"])
        self.assertFalse(payload["hidden_axiom_adopted"])

    def test_markdown_reports_obstruction(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Canonical/Liouville det equals one: True", markdown)
        self.assertIn("Phase-space route selects J_phi: False", markdown)
        self.assertIn("Requires Hamiltonian/source branch: True", markdown)
        self.assertIn("Uses Q_det/Q_cross absorption: False", markdown)
        self.assertIn("Hidden axiom adopted: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
