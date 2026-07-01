from __future__ import annotations

import unittest

from scripts.build_p0_eft_primordial_ward_coefficient_solver import build_payload


class P0EFTPrimordialWardCoefficientSolverTests(unittest.TestCase):
    def test_ward_system_closes_to_one_parameter_family(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "primordial-ward-coefficient-solver-recorded")
        self.assertTrue(payload["coefficients_closed_up_to_one_topological_amplitude"])
        self.assertEqual(payload["solution_family"]["c_sound"], "theta")
        self.assertEqual(payload["solution_family"]["c_opacity"], "-theta")
        self.assertEqual(payload["solution_family"]["c_geff"], "-2*theta")
        self.assertEqual(payload["solution_family"]["c_immirzi"], "-2*theta")

    def test_amplitude_is_not_yet_no_fit(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["amplitude_numerically_fixed"])
        self.assertFalse(payload["derived_geometry_ready"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
