from __future__ import annotations

import unittest

from scripts.build_p0_local_low_derivative_scalar_tensor_no_go_expansion import (
    build_payload,
    render_markdown,
)


class P0LocalLowDerivativeScalarTensorNoGoExpansionTests(unittest.TestCase):
    def test_expands_no_go_without_claiming_full_theorem(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "scalar-tensor-no-go-expanded-full-theorem-open")
        self.assertTrue(payload["restricted_scalar_no_go_proved"])
        self.assertFalse(payload["tracefree_source_provenance_closed"])
        self.assertTrue(payload["ghost_gate_available"])
        self.assertTrue(payload["source_derived_action_missing"])
        self.assertFalse(payload["accepted_candidate_exists"])
        self.assertFalse(payload["full_local_low_derivative_theorem_proved"])
        self.assertFalse(payload["prediction_ready"])

    def test_surviving_families_are_explicit(self) -> None:
        survivors = set(build_payload()["surviving_families"])

        self.assertIn("tracefree_tensor_H_TF", survivors)
        self.assertIn("derivative_strain", survivors)
        self.assertIn("curvature_dependent", survivors)
        self.assertIn("nonlocal_kernel", survivors)

    def test_markdown_reports_no_go_expansion(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Scalar/Tensor No-Go", markdown)
        self.assertIn("Full local low-derivative theorem proved: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
