import unittest

import numpy as np

from src.janus_lab.z2_sigma_homothetic_collar import (
    homothetic_collar_radius_selection_status,
    homothetic_constant_regular_payload,
    homothetic_endpoint_defect_values,
    reciprocal_projective_endpoint_defect_values,
)


class Z2SigmaHomotheticCollarTests(unittest.TestCase):
    def test_endpoint_defect_is_lambda_independent(self):
        values = homothetic_endpoint_defect_values(
            lambda_grid=[0.5, 1.0, 2.0],
            q_plus=np.eye(2),
            q_minus=[[2.0, 0.0], [0.0, 1.0]],
            tau_pullback=np.eye(2),
        )

        self.assertEqual(values.tolist(), [0.5, 0.5, 0.5])

    def test_constant_regular_payload_has_no_unique_radius(self):
        payload = homothetic_constant_regular_payload(
            lambda_grid=[0.5, 1.0, 2.0],
            endpoint_defect=[0.5, 0.5, 0.5],
            normal_holonomy_defect=1.0,
        )
        status = homothetic_collar_radius_selection_status(payload["F_reg"])

        self.assertEqual(payload["F_reg"], [1.5, 1.5, 1.5])
        self.assertEqual(payload["regularity_roots"], [])
        self.assertFalse(payload["R_Sigma_over_ell_collar_selected"])
        self.assertTrue(status["F_reg_lambda_independent"])
        self.assertFalse(status["radius_selection_possible"])

    def test_reciprocal_projective_endpoint_defect_selects_lambda_one(self):
        values = reciprocal_projective_endpoint_defect_values(lambda_grid=[0.5, 1.0, 2.0])

        self.assertGreater(values[0], 0.0)
        self.assertEqual(values[1], 0.0)
        self.assertGreater(values[2], 0.0)


if __name__ == "__main__":
    unittest.main()
