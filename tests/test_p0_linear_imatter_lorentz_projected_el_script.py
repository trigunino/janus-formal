from __future__ import annotations

import unittest

from scripts.build_p0_linear_imatter_lorentz_projected_el import build_payload


class P0LinearImatterLorentzProjectedELTests(unittest.TestCase):
    def test_lorentz_projection_closed_but_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "lorentz-projected-el-closed-algebraic")
        self.assertTrue(payload["raw_e_l_available"])
        self.assertTrue(payload["lorentz_projected_e_l_closed"])
        self.assertFalse(payload["fixes_l_uniquely"])
        self.assertFalse(payload["split_noether_residuals_evaluated"])
        self.assertFalse(payload["prediction_ready"])

    def test_projection_rows_cover_raw_generator_antisym_and_symmetric_rejection(self) -> None:
        text = " ".join(row["formula"] + row["status"] for row in build_payload()["projection_rows"])

        self.assertIn("P_mu^a", text)
        self.assertIn("Omega_ab=-Omega_ba", text)
        self.assertIn("antisym_ab", text)
        self.assertIn("sym_ab", text)
        self.assertIn("constraint-leak", text)


if __name__ == "__main__":
    unittest.main()
