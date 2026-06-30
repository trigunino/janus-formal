from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_kinetic_moment_sheet_limit import build_payload


class P0KineticMomentSheetLimitTests(unittest.TestCase):
    def test_sheet_sum_is_cold_kinetic_limit_not_prediction(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["sheet_sum_derived_as_cold_kinetic_limit"])
        self.assertTrue(decision["arbitrary_sheet_weights_removed"])
        self.assertFalse(decision["kinetic_transport_derived_from_janus"])
        self.assertFalse(payload["prediction_ready"])

    def test_moment_chain_recovers_sheet_stress(self) -> None:
        payload = build_payload()
        formulas = " ".join(row["formula"] for row in payload["moment_chain"])

        self.assertIn("int p^mu p^nu", formulas)
        self.assertIn("sum_s w_s", formulas)
        self.assertIn("sum_s rho_s_to", formulas)

    def test_obligations_include_optical_same_distribution(self) -> None:
        payload = build_payload()
        obligations = " ".join(payload["closure_obligations"])

        self.assertIn("same f_to", obligations)
        self.assertIn("mirror kinetic distribution", obligations)


if __name__ == "__main__":
    unittest.main()
