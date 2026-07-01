from __future__ import annotations

import unittest

from scripts.build_p0_eft_desi_dh_inverse_hubble_diagnostic import build_payload


class P0EFTDESIDHInverseHubbleDiagnosticTests(unittest.TestCase):
    def test_inverse_hubble_diagnostic_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "desi-dh-inverse-hubble-diagnostic-computed")
        self.assertGreater(len(payload["rows"]), 0)
        self.assertGreater(payload["required_multiplier_max"], 0.0)

    def test_linear_fit_is_reported(self) -> None:
        fit = build_payload()["linear_multiplier_fit"]

        self.assertIn("intercept", fit)
        self.assertIn("slope", fit)
        self.assertGreaterEqual(fit["rms"], 0.0)


if __name__ == "__main__":
    unittest.main()
