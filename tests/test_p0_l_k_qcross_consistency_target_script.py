from __future__ import annotations

import unittest

from scripts.build_p0_l_k_qcross_consistency_target import build_payload


class P0LKQCrossConsistencyTargetTests(unittest.TestCase):
    def test_target_remains_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "target-open")
        self.assertFalse(payload["lorentz_tetrad_compatibility_proved"])
        self.assertFalse(payload["k_transport_induced"])
        self.assertFalse(payload["same_map_for_k_and_qcross"])
        self.assertFalse(payload["residuals_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_l_requirements_are_lorentz_and_tetrad_compatible(self) -> None:
        requirements = " ".join(build_payload()["admissible_l_requirements"])

        self.assertIn("L_minus_to_plus^T eta L_minus_to_plus = eta", requirements)
        self.assertIn("L_plus_to_minus^T eta L_plus_to_minus = eta", requirements)
        self.assertIn("tetrad components", requirements)

    def test_k_and_qcross_share_same_transport_map(self) -> None:
        payload = build_payload()
        induced = " ".join(payload["induced_stress_requirements"])
        qcross = " ".join(payload["qcross_requirements"])

        self.assertIn("K_plus", induced)
        self.assertIn("K_minus", induced)
        self.assertIn("same L maps", induced)
        self.assertIn("L_minus_to_plus", qcross)
        self.assertIn("cannot differ from the Bianchi K transport map", qcross)

    def test_l_geom_and_scalar_absorption_are_forbidden(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("L_geom=e_plus E_minus", forbidden)
        self.assertIn("L_geom^T eta L_geom=eta", forbidden)
        self.assertIn("scalar Q_det", forbidden)
        self.assertIn("scalar Q_cross", forbidden)

    def test_residual_closure_is_required_before_prediction(self) -> None:
        payload = build_payload()
        obligations = " ".join(payload["open_proof_obligations"])
        induced = " ".join(payload["induced_stress_requirements"])

        self.assertIn("R_plus=0", obligations)
        self.assertIn("R_minus=0", obligations)
        self.assertIn("R_plus^A=0 and R_minus^A=0", induced)


if __name__ == "__main__":
    unittest.main()
