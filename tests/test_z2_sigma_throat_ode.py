import unittest

import numpy as np

from src.janus_lab.z2_sigma_throat_ode import (
    normalized_throat_ode_residual,
    solve_minimal_ci_throat_family,
)


class Z2SigmaThroatODETests(unittest.TestCase):
    def test_normalized_profile_solves_closed_ode(self):
        grid = np.array([0.0, 0.25, 0.5, 1.0, 1.5], dtype=float)
        residual = normalized_throat_ode_residual(grid)

        self.assertLess(float(np.max(np.abs(residual))), 1.0e-12)

    def test_minimal_ci_fix_shape_but_not_R0(self):
        payload = solve_minimal_ci_throat_family(
            rho_grid=[0.0, 0.25, 0.5, 1.0],
            R0_values=[0.5, 1.0, 2.0],
        )

        self.assertTrue(payload["normalized_solution_unique_under_minimal_CI"])
        self.assertTrue(payload["throat_is_minimal"])
        self.assertFalse(payload["R0_unique"])
        self.assertTrue(payload["R0_scale_degenerate"])
        self.assertTrue(payload["distinct_physical_profiles_sampled"])
        self.assertLess(payload["normalized_reconstruction_error_max_abs"], 1.0e-12)


if __name__ == "__main__":
    unittest.main()
