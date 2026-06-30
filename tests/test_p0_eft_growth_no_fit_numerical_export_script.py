from __future__ import annotations

import unittest

from scripts.build_p0_eft_growth_no_fit_numerical_export import (
    branch_constants,
    build_payload,
    derived_omega_m0,
    integrate_growth,
    integrate_radion,
)


class P0EFTGrowthNoFitNumericalExportTests(unittest.TestCase):
    def test_branch_constants_satisfy_atanh_bound(self) -> None:
        constants = branch_constants()

        self.assertTrue(constants["existence_bound_satisfied"])
        self.assertGreater(constants["chi_inf"], 0)
        self.assertGreater(constants["Lambda_J"], 0)

    def test_radion_profile_generates_omega_t(self) -> None:
        rows = integrate_radion(branch_constants())

        self.assertGreater(len(rows), 10)
        self.assertTrue(any(row["Omega_T"] > 0 for row in rows))

    def test_growth_curve_is_generated(self) -> None:
        constants = branch_constants()
        rows = integrate_growth(constants, integrate_radion(constants))

        self.assertGreater(len(rows), 10)
        self.assertIn("fsigma8_shape", rows[-1])

    def test_status_is_conditional_not_global(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["fsigma8_prediction_no_fit_ready_conditionally"])
        self.assertIn("full_cosmology_prediction_ready", status)

    def test_omega_m0_is_derived_from_friedmann(self) -> None:
        constants = branch_constants()
        omega_m0 = derived_omega_m0(constants, integrate_radion(constants))

        self.assertIsInstance(omega_m0, float)


if __name__ == "__main__":
    unittest.main()
