from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_m30_z2_symmetric_force_cancellation import (
    build_payload,
    render_markdown,
)


class M30Z2SymmetricForceCancellationTests(unittest.TestCase):
    def test_strict_z2_cancels_bulk_force(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["formulae"]["force_after_Z2"], "F_Sigma = 0")
        self.assertFalse(
            payload["consequences"]["bulk_M30_interaction_generates_sigma_counterterm_under_strict_Z2"]
        )

    def test_nonzero_counterterm_requires_defect_or_asymmetry(self) -> None:
        payload = build_payload()

        self.assertTrue(
            payload["consequences"]["need_independent_tunnel_defect_action_for_nonzero_E_counterterm"]
        )
        self.assertIn("localized Sigma defect", payload["formulae"]["nonzero_force_requires"])

    def test_markdown_records_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Z2-Symmetric Force Cancellation", markdown)
        self.assertIn("localized throat defect", markdown)


if __name__ == "__main__":
    unittest.main()
