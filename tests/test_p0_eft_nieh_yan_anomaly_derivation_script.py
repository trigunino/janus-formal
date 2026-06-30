from __future__ import annotations

import unittest

from scripts.build_p0_eft_nieh_yan_anomaly_derivation import build_payload, render_markdown


class P0EFTNiehYanAnomalyDerivationTests(unittest.TestCase):
    def test_eta_identity_closes_under_trace_normalization(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["derivation"]["eta_H"], "-2")
        self.assertEqual(payload["derivation"]["identity_residual_eta_H_plus_2"], "0")
        self.assertTrue(
            payload["theorem_status"][
                "eta_H_plus_2_identity_closed_under_standard_trace_normalization"
            ]
        )

    def test_global_normalization_remains_explicit_input(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["trace_normalization_still_an_input"])
        self.assertFalse(status["no_fit_lock_ready_from_eta_alone"])

    def test_markdown_names_trace_lock(self) -> None:
        self.assertIn("eta_H=-2", render_markdown(build_payload()))


if __name__ == "__main__":
    unittest.main()
