from __future__ import annotations

import unittest

from scripts.build_p0_nonmetricity_integrability_curl_gate import (
    build_payload,
    render_markdown,
)


class P0NonmetricityIntegrabilityCurlGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "nonmetricity-integrability-curl-gate-open")
        self.assertTrue(payload["n_definition_closed"])
        self.assertTrue(payload["flat_integrability_toy_closed"])
        self.assertTrue(payload["curl_defect_rejected"])
        self.assertEqual(payload["numeric_probe"], "p0_nonmetricity_curl_numeric_probe")
        self.assertTrue(payload["numeric_probe_available"])
        self.assertFalse(payload["source_n_integrability_proved"])
        self.assertFalse(payload["mirror_integrability_proved"])
        self.assertFalse(payload["prediction_ready"])

    def test_toy_curl_rejects_nonintegrable_n(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["compatible_toy"]["curl"], "0")
        self.assertTrue(payload["compatible_toy"]["passes"])
        self.assertEqual(payload["curl_defect_toy"]["curl"], "-x")
        self.assertFalse(payload["curl_defect_toy"]["passes"])

    def test_covariant_identity_and_acceptance_tests_are_explicit(self) -> None:
        payload = build_payload()
        tests = " ".join(payload["acceptance_tests"])

        self.assertIn("[D_alpha,D_beta]H", payload["covariant_identity"])
        self.assertIn("one same H", tests)
        self.assertIn("same Gamma/Omega branch", tests)
        self.assertIn("H^{-1}", tests)
        self.assertIn("no curl defect", tests)

    def test_markdown_reports_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Nonmetricity Integrability Curl", markdown)
        self.assertIn("p0_nonmetricity_curl_numeric_probe", markdown)
        self.assertIn("curl=-x", markdown)
        self.assertIn("Source N integrability proved: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
