from __future__ import annotations

import unittest

from scripts.build_p0_dust_fixed_current_density_response import build_payload


class P0DustFixedCurrentDensityResponseTests(unittest.TestCase):
    def test_fixed_current_branch_closed_only(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "fixed-current-density-response-closed-branch-only")
        self.assertTrue(payload["fixed_vector_current_branch_closed"])
        self.assertFalse(payload["densitized_current_branch_closed"])
        self.assertTrue(payload["densitized_current_density_response_available"])
        self.assertFalse(payload["janus_pullback_branch_closed"])
        self.assertFalse(payload["transverse_velocity_response_derived"])
        self.assertFalse(payload["full_dust_delta_g_t_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_derivation_contains_density_formula_and_warning(self) -> None:
        text = " ".join(row["formula"] + row["status"] for row in build_payload()["derivation_rows"])

        self.assertIn("rho^2", text)
        self.assertIn("delta_g rho", text)
        self.assertIn("fixed-current", text)
        self.assertIn("sqrt(-g)N^mu", text)
        self.assertIn("separate-branch-required", text)


if __name__ == "__main__":
    unittest.main()
