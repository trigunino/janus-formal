from __future__ import annotations

import unittest

from scripts.build_p0_eft_kink_source_closure_audit import build_payload, render_markdown


class P0EFTKinkSourceClosureAuditTests(unittest.TestCase):
    def test_audit_closes_derivative_source_not_prediction(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["derivative_jump_source_closed"])
        self.assertTrue(status["skink_formula_encoded"])
        self.assertFalse(status["skink_coefficient_derived"])
        self.assertFalse(status["alpha_Janus_derived"])
        self.assertFalse(status["kink_source_promotable"])

    def test_audit_tracks_isotropic_alpha_as_conditional(self) -> None:
        payload = build_payload()

        self.assertIn("7/6", payload["conditional_piece"])
        self.assertIn("rho_torsion_eff", " ".join(payload["open_blockers"]))

    def test_markdown_keeps_promotion_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("kink_source_promotable: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
