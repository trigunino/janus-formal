from __future__ import annotations

import unittest

from src.janus_lab.z2_null_sigma_pt_bridge import (
    null_sigma_pt_bridge_source_alignment_payload,
)


class Z2NullSigmaPTBridgeTests(unittest.TestCase):
    def test_source_alignment_separates_regular_sigma_pipeline(self) -> None:
        payload = null_sigma_pt_bridge_source_alignment_payload()

        self.assertEqual(payload["branch"], "Z2_null_Sigma_PT_bridge")
        self.assertTrue(payload["branch_claims"]["drdt_cross_term_retained"])
        self.assertTrue(payload["branch_claims"]["degenerate_or_null_throat_allowed"])
        self.assertFalse(payload["hard_separation_from_regular_sigma"]["regular_h_ab_K_ab_pipeline_allowed"])
        self.assertFalse(payload["current_status"]["null_boundary_variables_declared"])

    def test_required_null_formalism_is_explicit(self) -> None:
        required = null_sigma_pt_bridge_source_alignment_payload()["required_null_formalism"]

        self.assertTrue(required["null_generator_l_required"])
        self.assertTrue(required["screen_metric_q_AB_required"])
        self.assertTrue(required["null_Bianchi_transport_required"])


if __name__ == "__main__":
    unittest.main()
