from __future__ import annotations

import unittest

from scripts.build_p0_pulled_dust_el_projection_substitution import build_payload


class P0PulledDustELProjectionSubstitutionTests(unittest.TestCase):
    def test_substitution_ledger_is_open_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "el-projection-substitution-open")
        self.assertFalse(payload["all_substitutions_closed"])
        self.assertFalse(payload["projected_cuu_from_el_closed"])
        self.assertFalse(payload["conditional_dust_branch_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_measure_dl_force_and_mirror(self) -> None:
        pieces = {row["piece"] for row in build_payload()["substitution_rows"]}

        self.assertIn("measure_density", pieces)
        self.assertIn("velocity_tetrad", pieces)
        self.assertIn("transverse_force", pieces)
        self.assertIn("mirror_inverse", pieces)

    def test_dependencies_point_to_existing_artifacts(self) -> None:
        deps = " ".join(row["depends_on"] for row in build_payload()["substitution_rows"])

        self.assertIn("dphi_density_cancellation", deps)
        self.assertIn("dl_velocity_cancellation", deps)
        self.assertIn("projected_cuu_map_force_balance", deps)
        self.assertIn("phi_l_convention_lock", deps)

    def test_sufficient_conditions_forbid_shortcut(self) -> None:
        conditions = " ".join(build_payload()["sufficient_conditions"])

        self.assertIn("derived from EL projection", conditions)
        self.assertIn("one phi/L convention", conditions)
        self.assertIn("pressure/Pi", conditions)


if __name__ == "__main__":
    unittest.main()
