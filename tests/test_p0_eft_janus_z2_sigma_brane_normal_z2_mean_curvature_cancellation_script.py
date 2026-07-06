from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_brane_normal_z2_mean_curvature_cancellation import (
    build_payload,
    render_markdown,
)


class BraneNormalZ2MeanCurvatureCancellationTests(unittest.TestCase):
    def test_z2_mean_curvature_closes_normal_force_equation(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["closure"]["mean_curvature_cancels"])
        self.assertTrue(payload["closure"]["normal_force_equation_closes_symbolically"])
        self.assertFalse(payload["closure"]["requires_DeltaK_values"])

    def test_defect_is_not_forced_by_normal_equation(self) -> None:
        consequence = build_payload()["consequence"]

        self.assertTrue(consequence["source_force_equation_closed_for_strict_Z2_transparent_branch"])
        self.assertFalse(consequence["tunnel_defect_forced_by_normal_brane_equation"])
        self.assertTrue(consequence["DeltaK_still_needed_for_junction_rho_p_and_RSigma"])

    def test_markdown_reports_mean_curvature(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Mean-Curvature Cancellation", markdown)
        self.assertIn("Kbar_ab = 0", markdown)


if __name__ == "__main__":
    unittest.main()
