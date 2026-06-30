from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_sheet_sum_dust_model import build_payload


class P0SheetSumDustModelTests(unittest.TestCase):
    def test_sheet_sum_defines_post_caustic_route_without_prediction(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["post_caustic_route_defined"])
        self.assertTrue(decision["single_diffeomorphism_replaced"])
        self.assertFalse(decision["new_fit_parameters"])
        self.assertFalse(payload["prediction_ready"])

    def test_model_sums_stress_residual_and_optics(self) -> None:
        payload = build_payload()
        formulas = " ".join(row["formula"] for row in payload["sheet_model"])

        self.assertIn("sum_s rho_s_to", formulas)
        self.assertIn("sum_s rho_s_to h_s C_s", formulas)
        self.assertIn("Q_cross_total", formulas)

    def test_obligations_forbid_sheet_specific_fit(self) -> None:
        payload = build_payload()
        obligations = " ".join(payload["closure_obligations"])

        self.assertIn("same-L", obligations)
        self.assertIn("conserve total transported mass", obligations)
        self.assertIn("not a physical fit", obligations)


if __name__ == "__main__":
    unittest.main()
