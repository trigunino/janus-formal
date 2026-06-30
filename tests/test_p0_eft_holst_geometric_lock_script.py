from __future__ import annotations

import unittest

from scripts.build_p0_eft_holst_geometric_lock import build_payload


class P0EFTHolstGeometricLockTests(unittest.TestCase):
    def test_observed_locks_are_encoded(self) -> None:
        payload = build_payload()
        locks = payload["locks"]

        self.assertEqual(locks["eta_H_observed"], -2.0)
        self.assertEqual(locks["a_sigma_observed"], "2/3")
        self.assertEqual(locks["z_sigma_observed"], "1/2")
        self.assertEqual(locks["eta_H_local_trace_identity_residual"], "0")
        self.assertEqual(locks["a_sigma_local_holonomy_identity_residual"], "0")

    def test_no_fit_remains_open_until_geometry_is_derived(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["holst_branch_observationally_accepted"])
        self.assertTrue(status["eta_H_local_trace_identity_closed"])
        self.assertTrue(status["a_sigma_local_holonomy_identity_closed"])
        self.assertFalse(status["aps_global_normalization_closed"])
        self.assertFalse(status["orbifold_global_cover_closed"])
        self.assertFalse(status["eta_H_derived_from_Holst_Nieh_Yan_trace"])
        self.assertFalse(status["a_sigma_derived_from_orbifold_holonomy"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
