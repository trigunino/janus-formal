from __future__ import annotations

import unittest

from scripts.build_p0_eft_ds_vector_boundary_ghost_audit import build_payload, render_markdown


class P0EFTDSVectorBoundaryGhostAuditTests(unittest.TestCase):
    def test_vector_boundary_ghost_is_closed_conditionally(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["vector_boundary_ghost_checked"])
        self.assertTrue(status["no_vector_boundary_ghost"])
        self.assertTrue(status["ds_stability_ready_conditionally"])
        self.assertFalse(status["prediction_ready_unconditional"])

    def test_no_kinetic_injection_is_recorded(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["result"]["new_longitudinal_boundary_kinetic_term"], False)
        self.assertIn("none at this order", payload["audit"]["kinetic_injection"])

    def test_next_obligation_is_matter(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("matter/Vlasov", obligations)
        self.assertIn("lensing/growth", obligations)

    def test_markdown_marks_ds_conditionally_ready(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("ds_stability_ready_conditionally: True", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
