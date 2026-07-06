from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_m30_bulk_to_sigma_distribution_reduction import (
    build_payload,
    render_markdown,
)


class M30BulkToSigmaDistributionReductionTests(unittest.TestCase):
    def test_derives_conditional_surface_force_not_counterterm(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["derived"]["normal_variation_formula_derived"])
        self.assertTrue(payload["derived"]["M30_interaction_can_source_sigma_force_conditionally"])
        self.assertFalse(payload["derived"]["explicit_counterterm_density_derived"])
        self.assertFalse(payload["gate_passed"])

    def test_formula_contains_normal_variation_and_force_density(self) -> None:
        formulae = build_payload()["formulae"]

        self.assertIn("delta_X A_int|Sigma", formulae["bulk_to_boundary_variation"])
        self.assertIn("sqrt|h|", formulae["surface_force_density"])
        self.assertIn("L_ct(R)", formulae["primitive_if_force_known"])

    def test_blocks_on_embedding_and_interaction_scalar_data(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["primary_blocker"], "active_embedding_X_pm")
        self.assertIn("normal_lapses_N_pm_on_Sigma", payload["blockers"])
        self.assertIn("interaction_scalars_Sbar_plus_S_minus_on_Sigma", payload["blockers"])

    def test_markdown_reports_conditional_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Bulk-to-Sigma", markdown)
        self.assertIn("conditional", markdown)
        self.assertIn("active embedding", markdown)


if __name__ == "__main__":
    unittest.main()
