from __future__ import annotations

import unittest

from scripts.build_p0_minimal_nonrustine_extension_contract import build_payload, render_markdown


class P0MinimalNonRustineExtensionContractTests(unittest.TestCase):
    def test_contract_is_not_adopted_and_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "minimal-nonrustine-extension-contract-not-adopted")
        self.assertFalse(payload["new_axiom_adopted"])
        self.assertTrue(payload["extension_allowed_only_if_zero_axiom_fails"])
        self.assertTrue(payload["must_be_declared_as_extension"])
        self.assertFalse(payload["can_be_used_for_prediction_now"])
        self.assertFalse(payload["prediction_ready"])

    def test_contract_forbids_rustines(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["forbids_qdet_qcross_absorption"])
        self.assertTrue(payload["forbids_lensing_fit_selection"])
        self.assertTrue(payload["requires_same_l"])
        self.assertTrue(payload["requires_mirror_inverse"])
        self.assertTrue(payload["requires_stability"])

    def test_markdown_reports_contract(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Non-Rustine Extension Contract", markdown)
        self.assertIn("New axiom adopted: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
