from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_closure_obligation_matrix import (
    build_payload,
    render_markdown,
)


class P0TracefreeHClosureObligationMatrixTests(unittest.TestCase):
    def test_matrix_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-closure-obligations-open")
        self.assertFalse(payload["accepted_as_prediction_input"])
        self.assertFalse(payload["source_selection_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_target_equation_is_stf_source_equation(self) -> None:
        payload = build_payload()

        self.assertIn("P_STF", payload["target_equation"])
        self.assertIn("E_H", payload["target_equation"])
        self.assertIn("S_TF^Janus", payload["target_equation"])

    def test_obligations_name_remaining_locks(self) -> None:
        rows = {row["obligation"]: row for row in build_payload()["obligations"]}

        self.assertIn("stf_source_type", rows)
        self.assertIn("stf_el_operator", rows)
        self.assertIn("source_provenance", rows)
        self.assertIn("scalar_vector_no_go", rows)
        self.assertIn("candidate_selection", rows)
        self.assertIn("curl_integrability", rows)
        self.assertIn("mirror_inverse", rows)
        self.assertIn("same_l_transport", rows)
        self.assertIn("gauge_boundary", rows)
        self.assertIn("ghost_stability", rows)
        self.assertTrue(rows["scalar_vector_no_go"]["closed"])
        self.assertFalse(any(row["closed"] for name, row in rows.items() if name != "scalar_vector_no_go"))

    def test_forbidden_shortcuts_block_trace_fit_and_screen_law(self) -> None:
        shortcuts = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("rho", shortcuts)
        self.assertIn("B4vol", shortcuts)
        self.assertIn("residual cancellation", shortcuts)
        self.assertIn("2D screen", shortcuts)
        self.assertIn("stability", shortcuts)

    def test_markdown_reports_obligation_matrix(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Trace-Free H Closure Obligation Matrix", markdown)
        self.assertIn("P_STF(E_H - S_TF^Janus)=0", markdown)
        self.assertIn("Obligations closed: 1/10", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
