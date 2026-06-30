from __future__ import annotations

import unittest

from scripts.build_p0_dust_monoflux_local_residual_stack import build_payload, render_markdown


class P0DustMonofluxLocalResidualStackTests(unittest.TestCase):
    def test_local_stack_closed_but_source_stack_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dust-monoflux-local-stack-closed-source-stack-open")
        self.assertTrue(payload["local_conditional_stack_closed"])
        self.assertTrue(payload["conditional_residual_algebra_ready"])
        self.assertFalse(payload["source_derived_stack_closed"])
        self.assertFalse(payload["r_plus_r_minus_source_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_all_local_rows_are_closed(self) -> None:
        rows = {row["row"]: row for row in build_payload()["local_rows"]}

        self.assertIn("cold_dust_branch", rows)
        self.assertIn("particle_geodesic_action", rows)
        self.assertIn("connection_difference_cuu", rows)
        self.assertIn("projected_cuu_substitution", rows)
        self.assertIn("dlogb4vol_product_identity", rows)
        self.assertIn("falpha_dl_identity", rows)
        self.assertTrue(all(row["closed"] for row in rows.values()))

    def test_source_rows_remain_open_and_named(self) -> None:
        rows = {row["row"]: row for row in build_payload()["source_rows"]}

        self.assertIn("shared_phi_j_source_selection", rows)
        self.assertIn("source_selected_measure", rows)
        self.assertIn("source_selected_jacobian", rows)
        self.assertIn("dynamic_phi_l_selection", rows)
        self.assertTrue(all(not row["closed"] for row in rows.values()))

    def test_forbidden_promotions_block_overclaim(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_promotions"])

        self.assertTrue(payload["dust_monoflux_only"])
        self.assertTrue(payload["multistream_forbidden"])
        self.assertTrue(payload["pressure_pi_excluded"])
        self.assertIn("source-derived Janus closure", forbidden)
        self.assertIn("shell crossing", forbidden)
        self.assertIn("pressure/Pi", forbidden)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Local conditional stack closed: True", markdown)
        self.assertIn("Source-derived stack closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
