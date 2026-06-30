from __future__ import annotations

import unittest

from scripts.build_p0_higher_derivative_dl_scouple_obstruction import (
    build_payload,
    render_markdown,
)


class P0HigherDerivativeDLScoupleObstructionTests(unittest.TestCase):
    def test_higher_derivative_terms_produce_pdes_but_not_unique_map(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "higher-derivative-dl-scouple-selector-open")
        self.assertTrue(payload["higher_derivative_terms_produce_pde"])
        self.assertFalse(payload["higher_derivative_terms_select_unique_phi_j_l"])
        self.assertTrue(all(row["produces_transport_pde"] for row in payload["rows"]))
        self.assertTrue(all(not row["selects_unique_map"] for row in payload["rows"]))

    def test_source_obligations_remain(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["requires_source_derived_coefficient"])
        self.assertTrue(payload["requires_source_or_boundary_data"])
        self.assertTrue(payload["requires_same_l_qcross_k_proof"])
        self.assertTrue(payload["requires_split_noether_proof"])
        self.assertTrue(payload["new_axiom_if_adopted_without_source"])

    def test_zero_rustine_guards_hold(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["hidden_axiom_used"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_pde_and_open_selection(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Higher-derivative terms produce PDE: True", markdown)
        self.assertIn("Higher-derivative terms select unique phi/J/L: False", markdown)
        self.assertIn("Requires source-derived coefficient: True", markdown)
        self.assertIn("fourth-order", markdown)


if __name__ == "__main__":
    unittest.main()
