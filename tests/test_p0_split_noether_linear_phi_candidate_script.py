from __future__ import annotations

import unittest

from scripts.build_p0_split_noether_linear_phi_candidate import build_payload


class P0SplitNoetherLinearPhiCandidateTests(unittest.TestCase):
    def test_linear_candidate_only_normalized_not_accepted_or_rejected(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "linear-candidate-normalized-variation-blocked")
        self.assertTrue(payload["c1_fixed_by_weak_sign"])
        self.assertFalse(payload["candidate_rejected"])
        self.assertFalse(payload["candidate_accepted"])
        self.assertTrue(payload["imatter_tensor_contract_defined"])
        self.assertTrue(payload["metric_measure_variation_available"])
        self.assertTrue(payload["l_variation_algebra_closed"])
        self.assertTrue(payload["lorentz_projected_e_l_closed"])
        self.assertFalse(payload["variation_blocked_by_missing_tensor_definition"])
        self.assertTrue(payload["variation_blocked_by_missing_variational_rules"])
        self.assertFalse(payload["split_noether_residuals_evaluated"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_metric_map_and_residual_blocks(self) -> None:
        rows = {row["row"]: row for row in build_payload()["candidate_rows"]}

        self.assertEqual(rows["candidate"]["formula"], "I_matter*c1")
        self.assertIn("c1=1", rows["weak_sign_normalization"]["formula"])
        self.assertIn("full K requires", rows["metric_variation"]["formula"])
        self.assertIn("pullback", rows["map_variation"]["formula"])
        self.assertIn("R_plus/R_minus", rows["split_noether_substitution"]["formula"])


if __name__ == "__main__":
    unittest.main()
