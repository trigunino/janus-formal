from __future__ import annotations

import unittest

from scripts.build_p0_nonmetricity_curl_numeric_probe import build_payload, render_markdown


class P0NonmetricityCurlNumericProbeTests(unittest.TestCase):
    def test_probe_is_bounded_non_predictive_and_references_symbolic_gate(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "nonmetricity-curl-numeric-probe-diagnostic")
        self.assertIn("p0_nonmetricity_integrability_curl_gate", payload["depends_on"])
        self.assertTrue(payload["n_is_computed_as_dh"])
        self.assertTrue(payload["scalar_and_matrix_h_supported"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_fitted_amplitude"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_scalar_and_matrix_dh_curls_close(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["all_compatible_curls_close"])
        self.assertEqual([case["name"] for case in payload["cases"]], ["scalar_H", "matrix_H_2x2"])
        for case in payload["cases"]:
            self.assertLess(case["compatible_curl"]["max_abs_curl"], 1e-10)

    def test_injected_curl_defects_fail(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["all_curl_defects_rejected"])
        for case in payload["cases"]:
            self.assertFalse(case["curl_defected_closes"])
            self.assertGreater(case["curl_defected"]["max_abs_curl"], 1e-3)

    def test_markdown_records_no_fit_and_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Nonmetricity Curl Numeric Probe", markdown)
        self.assertIn("p0_nonmetricity_integrability_curl_gate", markdown)
        self.assertIn("Uses observational fit: False", markdown)
        self.assertIn("Uses fitted amplitude: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
