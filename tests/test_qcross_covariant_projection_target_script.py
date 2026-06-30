from __future__ import annotations

import unittest

from scripts.build_qcross_covariant_projection_target import build_payload


class QCrossCovariantProjectionTargetTests(unittest.TestCase):
    def test_payload_keeps_cross_map_missing(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["physics_closed"])
        self.assertIn("M_minus_to_plus", payload["target"]["negative_optical_projection"])
        self.assertIn("L_minus_to_plus", payload["target"]["map_induction"])
        self.assertTrue(any("M_minus_to_plus" in item for item in payload["missing_maps"]))
        self.assertTrue(any("L_minus_to_plus" in item for item in payload["missing_maps"]))
        self.assertIn("rho_s + p_s", payload["target"]["perfect_fluid_contraction"])
        self.assertEqual(payload["target"]["q_cross"], "Q_cross = A_minus / A_plus")

    def test_local_velocity_bridge_is_only_a_reduction(self) -> None:
        payload = build_payload()
        reductions = {row["case"]: row for row in payload["reductions"]}

        self.assertIn("gamma_minus^2", reductions["local_positive_orthonormal_frame"]["result"])
        self.assertEqual(
            reductions["local_positive_orthonormal_frame"]["status"],
            "implemented diagnostic reduction",
        )


if __name__ == "__main__":
    unittest.main()
