from __future__ import annotations

import unittest

from scripts.build_p0_cuu_jacobian_curl_numeric_probe import build_payload, render_markdown


class P0CuuJacobianCurlNumericProbeTests(unittest.TestCase):
    def test_probe_distinguishes_true_jacobian_from_pointwise_defect(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "cuu-jacobian-curl-numeric-probe-diagnostic")
        self.assertTrue(payload["compatible_jacobian_curl_closes"])
        self.assertFalse(payload["curl_defected_jacobian_curl_closes"])
        self.assertTrue(payload["jacobian_is_from_phi_in_compatible_case"])
        self.assertTrue(payload["defected_jacobian_is_pointwise_only"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_defected_residual_is_nonzero(self) -> None:
        payload = build_payload()

        self.assertLess(payload["compatible_jacobian"]["max_abs_curl"], 1e-10)
        self.assertGreater(payload["curl_defected_jacobian"]["max_abs_curl"], 1e-3)

    def test_no_fit_or_scalar_absorption(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])

    def test_markdown_records_open_physical_gate(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Compatible Jacobian curl closes: True", markdown)
        self.assertIn("Curl-defected Jacobian curl closes: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
