from __future__ import annotations

import unittest

from scripts.build_p0_bianchi_minimal_full_connection_lift_system import build_payload


class P0BianchiMinimalFullConnectionLiftSystemTests(unittest.TestCase):
    def test_lift_system_is_open_but_flow_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "full-connection-lift-system-open")
        self.assertTrue(payload["local_flow_closed"])
        self.assertTrue(payload["eta_antisymmetry_closed"])
        self.assertTrue(payload["spin_connection_identity_algebra_closed"])
        self.assertFalse(payload["spin_connection_identity_source_selected"])
        self.assertTrue(payload["curvature_commutator_identity_closed"])
        self.assertTrue(payload["relative_curvature_formula_closed"])
        self.assertFalse(payload["transverse_boost_selected"])
        self.assertFalse(payload["spatial_rotation_selected"])
        self.assertFalse(payload["curvature_integrability_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_decomposition_shows_selected_and_free_parts(self) -> None:
        rows = {row["piece"]: row for row in build_payload()["decomposition"]}

        self.assertTrue(rows["flow_boost"]["selected"])
        self.assertFalse(rows["transverse_boost_one_forms"]["selected"])
        self.assertFalse(rows["spatial_rotation_connection"]["selected"])
        self.assertFalse(rows["full_connection"]["selected"])
        self.assertIn("rank-one dust source is blind", rows["spatial_rotation_connection"]["reason"])

    def test_equation_system_contains_integrability_and_mirror(self) -> None:
        equations = " ".join(build_payload()["equation_system"])

        self.assertIn("u^alpha A_alpha = a_req", equations)
        self.assertIn("[D_alpha,D_beta]L=R_s,alpha_beta L - L R_o,alpha_beta", equations)
        self.assertIn("F_relative_alpha_beta=R_s,alpha_beta - L R_o,alpha_beta L^{-1}", equations)
        self.assertIn("D_[alpha Omega_beta]", equations)
        self.assertIn("F_relative_alpha_beta", equations)
        self.assertIn("D_alpha L=Omega_alpha L", equations)
        self.assertIn("partial_alpha L+omega_s,alpha L-L omega_o,alpha", equations)
        self.assertIn("mirror Bianchi residual", equations)

    def test_acceptance_tests_prevent_prediction_shortcut(self) -> None:
        tests = {row["test"]: row for row in build_payload()["acceptance_tests"]}

        self.assertTrue(tests["local_flow"]["passed"])
        self.assertTrue(tests["eta_antisymmetry"]["passed"])
        self.assertFalse(tests["curvature_integrability"]["passed"])
        self.assertFalse(tests["mirror_inverse"]["passed"])
        self.assertFalse(tests["same_l_qcross"]["passed"])


if __name__ == "__main__":
    unittest.main()
