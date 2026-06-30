from __future__ import annotations

import unittest

from scripts.build_p0_dlogb_4volume_obstruction import build_payload


class P0DlogB4VolumeObstructionTests(unittest.TestCase):
    def test_obstruction_is_written_but_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "obstruction-open")
        self.assertTrue(payload["b4vol_separated_from_v3_dust"])
        self.assertTrue(payload["lapse_terms_included"])
        self.assertTrue(payload["slice_terms_included"])
        self.assertTrue(payload["product_rule_terms_written"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_plus_and_minus_dlogb_identities_include_lapse_and_slice_terms(self) -> None:
        rows = {row["identity"]: row for row in build_payload()["dlogb_identities"]}

        self.assertIn("D_plus_alpha log B_4vol_plus_from_minus", rows)
        self.assertIn("D_minus_alpha log B_4vol_minus_from_plus", rows)
        text = " ".join(row["expanded"] for row in rows.values())
        self.assertIn("D_plus_alpha log N_minus", text)
        self.assertIn("D_minus_alpha log N_plus", text)
        self.assertIn("D_plus_alpha log gamma_minus", text)
        self.assertIn("D_minus_alpha log gamma_plus", text)

    def test_product_rule_terms_are_explicit_in_both_residuals(self) -> None:
        text = " ".join(row["term"] for row in build_payload()["residual_product_rules"])

        self.assertIn("R_plus", {row["residual"] for row in build_payload()["residual_product_rules"]})
        self.assertIn("R_minus", {row["residual"] for row in build_payload()["residual_product_rules"]})
        self.assertIn("D_plus_alpha(B_4vol_plus_from_minus K_minus_to_plus)", text)
        self.assertIn("K_minus_to_plus D_plus_alpha B_4vol_plus_from_minus", text)
        self.assertIn("D_minus_alpha(B_4vol_minus_from_plus K_plus_to_minus)", text)
        self.assertIn("K_plus_to_minus D_minus_alpha B_4vol_minus_from_plus", text)

    def test_forbids_scalar_or_raw_ratio_patch(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_replacements"])

        self.assertIn("V3_dust", forbidden)
        self.assertIn("raw a-ratio", forbidden)
        self.assertIn("Q_cross", forbidden)
        self.assertIn("Q_det", forbidden)

    def test_lists_missing_source_derived_identities(self) -> None:
        missing = " ".join(build_payload()["missing_source_identities"])

        self.assertIn("lapse", missing)
        self.assertIn("slice determinants", missing)
        self.assertIn("FLRW a-ratio", missing)
        self.assertIn("K residual cancellation", missing)
        self.assertIn("mirror identity", missing)


if __name__ == "__main__":
    unittest.main()
