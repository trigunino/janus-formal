from __future__ import annotations

import unittest

from scripts.build_qcross_tetrad_map_target import build_payload


class QCrossTetradMapTargetTests(unittest.TestCase):
    def test_tetrad_map_defines_qcross_without_closing_physics(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "map-target")
        self.assertFalse(payload["physics_closed"])
        self.assertIn("L_geom", payload["definitions"]["raw_geometric_solder_map"])
        self.assertIn("L_minus_to_plus", payload["definitions"]["transported_negative_velocity"])
        self.assertIn("Q_cross", payload["definitions"]["q_cross"])

    def test_map_requirements_keep_qdet_separate(self) -> None:
        requirements = " ".join(build_payload()["map_requirements"])

        self.assertIn("L_geom^T eta L_geom - eta", requirements)
        self.assertIn("admissible optical L_minus_to_plus must preserve eta_AB", requirements)
        self.assertIn("time-orientation preserving", requirements)
        self.assertIn("Q_det density/volume factors are not part", requirements)

    def test_local_velocity_formula_is_only_reduction(self) -> None:
        reductions = {row["case"]: row for row in build_payload()["reductions"]}

        self.assertEqual(
            reductions["flrw_aligned_comoving_tetrads"]["result"],
            "Q_cross=1",
        )
        self.assertIn("warning", reductions["raw_geometric_solder_map"]["result"])
        self.assertIn("gamma_minus^2", reductions["identity_frame_map"]["result"])
        self.assertEqual(reductions["equal_projection"]["result"], "Q_cross=1")

    def test_nontrivial_l_requires_bianchi_transport_compatibility(self) -> None:
        blockers = " ".join(build_payload()["blockers"])

        self.assertIn("M_minus_to_plus", blockers)
        self.assertIn("K_plus", blockers)
        self.assertIn("M_plus_to_minus/K_minus", blockers)
        self.assertIn("R_plus/R_minus", blockers)


if __name__ == "__main__":
    unittest.main()
