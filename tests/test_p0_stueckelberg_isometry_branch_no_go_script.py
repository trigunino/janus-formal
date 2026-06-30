from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_isometry_branch_no_go import build_payload


class P0StueckelbergIsometryBranchNoGoTests(unittest.TestCase):
    def test_isometry_cancels_connection_but_is_not_generic_janus(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["connection_residual_cancelled_if_isometry"])
        self.assertFalse(payload["generic_janus_admissible"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_no_go_preserves_two_metric_content(self) -> None:
        payload = build_payload()
        reasons = " ".join(payload["no_go_reasons"])

        self.assertIn("distinct sector scale factors", reasons)
        self.assertIn("two-metric content", reasons)
        self.assertTrue(payload["new_axiom_if_used_generically"])

    def test_next_derivation_requires_weaker_condition(self) -> None:
        payload = build_payload()

        self.assertIn("weaker map equation", payload["next_required_derivation"])
        self.assertIn("dust congruence", payload["next_required_derivation"])


if __name__ == "__main__":
    unittest.main()
