from __future__ import annotations

import unittest

from scripts.build_p0_sigma_dh_equivalence_gate import build_payload, render_markdown


class P0SigmaDHEquivalenceGateTests(unittest.TestCase):
    def test_equivalence_is_closed_but_source_selection_open(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "sigma-dh-equivalence-closed-source-selection-open",
        )
        self.assertTrue(payload["identity_closed"])
        self.assertFalse(payload["sigma_is_independent_knob"])
        self.assertFalse(payload["source_selection_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_forward_and_inverse_identities_are_present(self) -> None:
        payload = build_payload()

        self.assertIn("D_alpha H", payload["forward_identity"])
        self.assertIn("Sigma_alpha", payload["forward_identity"])
        self.assertIn("L_geom^{-T}", payload["inverse_identity"])
        self.assertIn("L_geom^{-1}", payload["inverse_identity"])
        self.assertIn("FrechetLog_H[D_alpha H]", payload["dq_identity"])

    def test_rules_block_double_counting_and_free_sigma(self) -> None:
        text = " ".join(build_payload()["equivalence_rules"])

        self.assertIn("choosing Sigma_alpha chooses D_alpha H", text)
        self.assertIn("choosing D_alpha H chooses", text)
        self.assertIn("eta-antisymmetric Lorentz part remains separate", text)
        self.assertIn("no independent Sigma_alpha and D_alpha H freedom", text)

    def test_allowed_and_forbidden_source_logic(self) -> None:
        payload = build_payload()
        allowed = " ".join(payload["allowed_source_selectors"])
        forbidden = " ".join(payload["forbidden_moves"])

        self.assertIn("published Janus source equation", allowed)
        self.assertIn("variational equation", allowed)
        self.assertIn("relative curvature", allowed)
        self.assertIn("cancel R_plus/R_minus", forbidden)
        self.assertIn("fit D_alpha H", forbidden)
        self.assertIn("independent Q connection", forbidden)

    def test_markdown_reports_remaining_lock(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Sigma / D H Equivalence", markdown)
        self.assertIn("Sigma is independent knob: False", markdown)
        self.assertIn("Allowed Source Selectors", markdown)
        self.assertIn("Remaining lock", markdown)


if __name__ == "__main__":
    unittest.main()
