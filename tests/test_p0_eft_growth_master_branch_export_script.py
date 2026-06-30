from __future__ import annotations

import unittest

from scripts.build_p0_eft_growth_master_branch_export import build_curve, build_payload, master_constants


class P0EFTGrowthMasterBranchExportTests(unittest.TestCase):
    def test_master_branch_uses_first_physical_coordinates(self) -> None:
        constants = master_constants()

        self.assertEqual(constants["eps"], -1.0)
        self.assertAlmostEqual(constants["rho_dS_residual"] / (3.0 * constants["Mpl2"] * constants["H2"]), 0.05)

    def test_curve_is_z0_to_z2(self) -> None:
        _, rows = build_curve()
        z_values = [row["z"] for row in rows]

        self.assertGreater(len(rows), 10)
        self.assertGreaterEqual(min(z_values), 0.0)
        self.assertLessEqual(max(z_values), 2.0)

    def test_branch_has_positive_matter(self) -> None:
        constants, _ = build_curve()

        self.assertGreater(constants["Omega_m0"], 0.05)

    def test_observation_comparison_is_not_claimed(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["observational_fsigma8_table_loaded"])
        self.assertFalse(status["direct_planck_sdss_eboss_desi_comparison_done"])


if __name__ == "__main__":
    unittest.main()
