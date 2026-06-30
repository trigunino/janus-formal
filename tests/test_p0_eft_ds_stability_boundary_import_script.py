from __future__ import annotations

import unittest

from scripts.build_p0_eft_ds_stability_boundary_import import build_payload, render_markdown


class P0EFTDSStabilityBoundaryImportTests(unittest.TestCase):
    def test_import_is_partial_until_vector_audit(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["boundary_conditions_imported"])
        self.assertTrue(status["tensor_sector_consistent_conditionally"])
        self.assertTrue(status["scalar_spinor_boundary_channel_consistent_conditionally"])
        self.assertFalse(status["vector_boundary_ghost_checked"])
        self.assertFalse(status["ds_stability_ready_conditionally"])

    def test_boundary_responses_are_listed(self) -> None:
        imported = build_payload()["imported_boundary"]

        self.assertEqual(imported["volume_response"], "lambda=-4*q_T")
        self.assertIn("beta*Delta_chi", imported["cartan_response"])
        self.assertIn("kappa", imported["nieh_yan_response"])

    def test_obligations_include_vector_and_scalar_recompute(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("vector/longitudinal", obligations)
        self.assertIn("scalar dS kinetic matrix", obligations)

    def test_markdown_keeps_ready_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("ds_stability_ready_conditionally: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
