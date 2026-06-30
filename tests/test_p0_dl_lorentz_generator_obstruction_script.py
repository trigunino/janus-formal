from __future__ import annotations

import unittest

from scripts.build_p0_dl_lorentz_generator_obstruction import build_payload


class P0DlLorentzGeneratorObstructionTests(unittest.TestCase):
    def test_obstruction_is_open_and_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "obstruction-open")
        self.assertTrue(payload["lorentz_generator_condition_derived"])
        self.assertFalse(payload["source_derived_generator"])
        self.assertFalse(payload["mirror_derivative_source_derived"])
        self.assertFalse(payload["same_l_for_k_and_qcross_source_derived"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["r_minus_closed"])
        self.assertFalse(payload["closure_claimed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_lorentz_generator_condition_is_derived_as_necessary(self) -> None:
        text = " ".join(
            f"{row['claim']} {row['derivation']}" for row in build_payload()["derivation_rows"]
        )

        self.assertIn("D_alpha(L^T eta L)=0", text)
        self.assertIn("D_alpha L_minus_to_plus = F_alpha L_minus_to_plus", text)
        self.assertIn("F_alpha^T eta + eta F_alpha=0", text)
        self.assertIn("necessary-not-source-derived", " ".join(row["status"] for row in build_payload()["derivation_rows"]))

    def test_mirror_derivative_and_shared_l_targets_are_present(self) -> None:
        text = " ".join(row["derivation"] for row in build_payload()["derivation_rows"])

        self.assertIn("L_plus_to_minus=L_minus_to_plus^{-1}", text)
        self.assertIn("D_alpha L_plus_to_minus", text)
        self.assertIn("K_plus/K_minus", text)
        self.assertIn("Q_cross", text)
        self.assertIn("same L_minus_to_plus and L_plus_to_minus maps", text)

    def test_residual_cancellation_terms_are_explicit_and_open(self) -> None:
        payload = build_payload()
        text = " ".join(
            term
            for row in payload["residual_cancellation_terms"]
            for term in row["needed_terms"]
        )

        self.assertTrue(all(not row["closed"] for row in payload["residual_cancellation_terms"]))
        self.assertIn("D_plus_alpha L_minus_to_plus", text)
        self.assertIn("D_minus_alpha L_plus_to_minus", text)
        self.assertIn("connection-difference", text)
        self.assertIn("D_plus_alpha log B_4vol_plus_from_minus", text)
        self.assertIn("D_minus_alpha log B_4vol_minus_from_plus", text)

    def test_missing_source_derived_identities_block_closure(self) -> None:
        payload = build_payload()
        missing = " ".join(payload["missing_source_derived_identities"])
        rules = " ".join(payload["rejection_rules"])

        self.assertIn("source-derived F_alpha", missing)
        self.assertIn("mirror transport law", missing)
        self.assertIn("same source-derived L maps", missing)
        self.assertIn("R_plus cancellation", missing)
        self.assertIn("R_minus cancellation", missing)
        self.assertIn("do not claim closure", rules)
        self.assertIn("do not publish a prediction", rules)


if __name__ == "__main__":
    unittest.main()
