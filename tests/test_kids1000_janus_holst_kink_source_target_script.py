from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_kink_source_target import build_payload


class KiDS1000JanusHolstKinkSourceTargetTests(unittest.TestCase):
    def test_payload_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "kink-source-target-open")
        self.assertFalse(payload["open_locks"]["skink_coefficient_derived"])
        self.assertFalse(payload["open_locks"]["alpha_Janus_derived"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["uses_kids_residuals"])
        self.assertFalse(payload["uses_bin_shift"])
        self.assertFalse(payload["uses_bin_factors"])
        self.assertEqual(payload["closure_audit_status"], "kink-source-closure-open")

    def test_payload_exposes_source_product_and_guards(self) -> None:
        payload = build_payload()

        self.assertIn("S_kink", payload["jump_operator"])
        self.assertIn("alpha_Janus", payload["jump_operator"])
        self.assertEqual(payload["sample_diagnostic_only"]["jump_amplitude"], [0.000125, 0.00025])
        self.assertIn("promote symbolic_scaffold", " ".join(payload["forbidden_shortcuts"]))
        self.assertIn("Euler/geodesic", " ".join(payload["source_closure_blockers"]))


if __name__ == "__main__":
    unittest.main()
