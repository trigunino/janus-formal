from __future__ import annotations

import unittest

from scripts.build_p0_m15_source_identity_implications import build_payload


class P0M15SourceIdentityImplicationsTests(unittest.TestCase):
    def test_m15_anchors_b4vol_but_not_closure(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["m15_checked"])
        self.assertTrue(payload["b4vol_definition_source_anchored"])
        self.assertFalse(payload["f_alpha_source_derived"])
        self.assertFalse(payload["dlogb_cancellation_source_derived"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["r_minus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_source_anchors_include_variation_field_equations_and_flrw_limit(self) -> None:
        text = " ".join(row["anchor"] + " " + row["content"] for row in build_payload()["source_anchors"])

        self.assertIn("Eq. 14", text)
        self.assertIn("delta g_plus", text)
        self.assertIn("Eqs. 23a-23b", text)
        self.assertIn("sqrt(-g_minus/-g_plus)", text)
        self.assertIn("Eq. 7", text)
        self.assertIn("a_plus", text)

    def test_blocker_implications_keep_f_and_dlogb_open(self) -> None:
        rows = {row["blocker"]: row for row in build_payload()["blocker_implications"]}

        self.assertEqual(rows["F_alpha"]["source_status"], "not supplied by M15")
        self.assertIn("does not define L_minus_to_plus", rows["F_alpha"]["reason"])
        self.assertEqual(rows["D log B_4vol"]["source_status"], "definition supplied, cancellation not supplied")
        self.assertIn("product-rule terms", rows["D log B_4vol"]["reason"])

    def test_rejection_rules_prevent_overclaiming_m15(self) -> None:
        rules = " ".join(build_payload()["rejection_rules"])

        self.assertIn("do not infer D_alpha L", rules)
        self.assertIn("FLRW", rules)
        self.assertIn("D log B_4vol", rules)
        self.assertIn("Q_cross", rules)


if __name__ == "__main__":
    unittest.main()
