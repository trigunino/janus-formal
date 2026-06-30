from __future__ import annotations

import unittest

from scripts.build_p0_route_d_tensor_derivative_admissibility_filter import (
    build_payload,
    render_markdown,
)


class P0RouteDTensorDerivativeAdmissibilityFilterTests(unittest.TestCase):
    def test_filter_excludes_free_tensor_derivative_routes(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tensor-derivative-admissibility-filter-open")
        self.assertEqual(payload["excluded_free_family_count"], 3)
        self.assertEqual(payload["open_conditional_family_count"], 1)
        self.assertFalse(payload["free_tracefree_tensor_allowed"])
        self.assertFalse(payload["free_derivative_operator_allowed"])
        self.assertTrue(payload["source_covariant_stf_operator_open"])
        self.assertFalse(payload["full_no_go_proved"])
        self.assertFalse(payload["prediction_ready"])

    def test_admissibility_gates_require_source_noether_same_l_and_stability(self) -> None:
        gates = " ".join(build_payload()["admissibility_gates"])

        self.assertIn("Janus source/action", gates)
        self.assertIn("Noether", gates)
        self.assertIn("same L", gates)
        self.assertIn("principal symbol", gates)
        self.assertIn("mirror", gates)

    def test_markdown_reports_filter(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Admissibility Filter", markdown)
        self.assertIn("Free tracefree tensor allowed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
