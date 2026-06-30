from __future__ import annotations

import unittest

from scripts.build_p0_janus_equations_to_dlogb4vol_closure_attempt import build_payload


class P0JanusEquationsToDlogB4volClosureAttemptTests(unittest.TestCase):
    def test_artifact_is_bounded_and_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "closure-attempt-open")
        self.assertTrue(payload["product_rule_identities_derived"])
        self.assertTrue(payload["source_slice_lapse_identities_missing"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_keeps_b4vol_v3_dust_rho_to_and_qdet_distinct(self) -> None:
        payload = build_payload()
        ledger = {row["symbol"]: row for row in payload["measure_ledger"]}

        self.assertTrue(payload["b4vol_v3_dust_rho_to_qdet_distinct"])
        for symbol in ("B_4vol", "V3_dust", "rho_to", "Q_det"):
            self.assertIn(symbol, ledger)
        self.assertIn("V3_dust", ledger["B_4vol"]["separate_from"])
        self.assertIn("rho_to", ledger["B_4vol"]["separate_from"])
        self.assertIn("Q_det", ledger["B_4vol"]["separate_from"])
        self.assertIn("B_4vol", ledger["Q_det"]["separate_from"])

    def test_uses_janus_source_determinant_and_bianchi_ingredients(self) -> None:
        payload = build_payload()
        ingredients = " ".join(
            row["source"] + " " + row["formula"] + " " + row["role"]
            for row in payload["janus_ingredients"]
        )

        self.assertTrue(payload["janus_source_determinant_bianchi_ingredients_listed"])
        self.assertIn("M15 Eqs. 4a-4b", ingredients)
        self.assertIn("B_4vol_plus_from_minus", ingredients)
        self.assertIn("B_4vol_minus_from_plus", ingredients)
        self.assertIn("Bianchi", ingredients)

    def test_product_rules_keep_dlogb_terms_explicit(self) -> None:
        identities = " ".join(row["identity"] for row in build_payload()["product_rule_identities"])

        self.assertIn("D_plus_nu log B_4vol_plus_from_minus", identities)
        self.assertIn("D_minus_nu log B_4vol_minus_from_plus", identities)
        self.assertIn("D_plus_nu(rho_minus_to_plus u_minus_to_plus^nu)", identities)
        self.assertIn("D_minus_nu(rho_plus_to_minus u_plus_to_minus^nu)", identities)

    def test_missing_identities_name_source_slice_lapse_and_transport(self) -> None:
        missing = " ".join(build_payload()["missing_identities"])

        self.assertIn("source identity", missing)
        self.assertIn("slice identity", missing)
        self.assertIn("lapse identity", missing)
        self.assertIn("transport law", missing)
        self.assertIn("velocity/tetrad identity", missing)

    def test_forbids_absorption_and_double_counting(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_operations"])

        self.assertTrue(payload["qdet_qcross_absorption_forbidden"])
        self.assertTrue(payload["double_counting_forbidden"])
        self.assertIn("absorb D log B_4vol into Q_det", forbidden)
        self.assertIn("absorb D log B_4vol into Q_cross", forbidden)
        self.assertIn("count B_4vol and V3_dust as the same determinant factor", forbidden)
        self.assertIn("after B_4vol has already weighted the source", forbidden)


if __name__ == "__main__":
    unittest.main()
