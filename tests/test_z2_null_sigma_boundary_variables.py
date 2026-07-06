from __future__ import annotations

import unittest

from src.janus_lab.z2_null_sigma_boundary_variables import null_sigma_boundary_variables_payload


class Z2NullSigmaBoundaryVariablesTests(unittest.TestCase):
    def test_null_vectors_are_declared_and_normalized(self) -> None:
        payload = null_sigma_boundary_variables_payload()

        self.assertEqual(payload["normalization"]["l_dot_l"], 0.0)
        self.assertEqual(payload["normalization"]["n_dot_n"], 0.0)
        self.assertEqual(payload["normalization"]["l_dot_n"], -1.0)
        self.assertTrue(payload["null_boundary_variables_declared"])
        self.assertFalse(payload["regular_hK_pipeline_allowed"])

    def test_stationary_so3_null_kinematics_are_explicit(self) -> None:
        kin = null_sigma_boundary_variables_payload()["SO3_null_kinematics"]

        self.assertEqual(kin["theta_l_expansion"], 0.0)
        self.assertEqual(kin["shear_l_AB"], 0.0)
        self.assertGreater(kin["inaffinity_kappa_l"], 0.0)


if __name__ == "__main__":
    unittest.main()
