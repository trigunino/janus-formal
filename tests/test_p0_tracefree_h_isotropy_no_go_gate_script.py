from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_isotropy_no_go_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHIsotropyNoGoGateTests(unittest.TestCase):
    def test_gate_rejects_isotropic_sources_as_prediction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-isotropy-no-go-open")
        self.assertTrue(payload["isotropic_sources_have_zero_tf_projection"])
        self.assertFalse(payload["flrw_selects_perturbative_tensor_closure"])
        self.assertFalse(payload["source_tracefree_h_selected"])
        self.assertFalse(payload["accepted_as_prediction_input"])
        self.assertFalse(payload["prediction_ready"])

    def test_rank_counts_keep_tracefree_target_explicit(self) -> None:
        ranks = build_payload()["rank_counts"]

        self.assertEqual(ranks["symmetric_H_components"], 10)
        self.assertEqual(ranks["tracefree_H_components"], 9)
        self.assertEqual(ranks["scalar_isotropic_channels"], 1)

    def test_each_isotropic_row_fails_to_select_q_tf(self) -> None:
        rows = build_payload()["rows"]

        self.assertGreaterEqual(len(rows), 4)
        self.assertTrue(all(not row["selects_q_tf"] for row in rows))

    def test_markdown_names_conditional_flrw_limit(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Trace-Free H Isotropy No-Go", markdown)
        self.assertIn("Q_TF=0", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
