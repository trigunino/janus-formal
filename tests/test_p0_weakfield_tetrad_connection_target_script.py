from __future__ import annotations

import unittest

from scripts.build_p0_weakfield_tetrad_connection_target import (
    build_payload,
    derive_connection_targets,
)


class P0WeakfieldTetradConnectionTargetTests(unittest.TestCase):
    def test_payload_is_restricted_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "restricted-weakfield-tetrad-connection-target")
        self.assertTrue(payload["connection_rows_computable"])
        self.assertTrue(payload["curvature_rows_recovered_symbolically"])
        self.assertFalse(payload["full_janus_tetrad_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["uses_observational_fit"])

    def test_boost_connection_uses_delta_phi_gradient(self) -> None:
        targets = derive_connection_targets()["boost_connection"]

        self.assertEqual(str(targets["Delta_omega_0x0"]), "dx_DeltaPhi")
        self.assertEqual(str(targets["Delta_omega_0y0"]), "dy_DeltaPhi")
        self.assertEqual(str(targets["Delta_omega_0z0"]), "dz_DeltaPhi")

    def test_spatial_rotation_uses_delta_psi_gradient(self) -> None:
        targets = derive_connection_targets()["spatial_rotation"]

        self.assertEqual(str(targets["Delta_omega_xyx"]), "dy_DeltaPsi")
        self.assertEqual(str(targets["Delta_omega_xyy"]), "-dx_DeltaPsi")
        self.assertEqual(str(targets["Delta_omega_xzx"]), "dz_DeltaPsi")

    def test_curvature_rows_recover_hessian_targets(self) -> None:
        targets = derive_connection_targets()

        self.assertEqual(str(targets["temporal_curvature_rows"]["Delta_F_0x0y"]), "H_DeltaPhi_xy")
        self.assertEqual(str(targets["spatial_curvature_rows"]["Delta_F_xyxy"]), "H_DeltaPsi_xx + H_DeltaPsi_yy")


if __name__ == "__main__":
    unittest.main()
