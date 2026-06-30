from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_qcross_geometric_tetrad_map_derivation import build_payload


class QCrossGeometricTetradMapDerivationTests(unittest.TestCase):
    def test_geometric_map_formula_is_recorded_without_closing_physics(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["algebra_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertIn("e_plus", payload["definitions"]["geometric_solder_map"])
        self.assertIn("E_minus", payload["definitions"]["geometric_solder_map"])

    def test_diagonal_flrw_raw_map_gives_lapse_ratio_warning(self) -> None:
        n_plus, n_minus, a_plus, a_minus = sp.symbols(
            "N_plus N_minus a_plus a_minus",
            positive=True,
        )
        l_geom = sp.diag(n_plus / n_minus, a_plus / a_minus)
        eta = sp.diag(-1, 1)
        compatibility = sp.simplify(l_geom.T * eta * l_geom)

        self.assertEqual(compatibility[0, 0], -(n_plus / n_minus) ** 2)
        self.assertEqual(compatibility[1, 1], (a_plus / a_minus) ** 2)
        self.assertIn(
            "Q_raw_geom=(N_plus/N_minus)^2",
            build_payload()["flrw_diagonal_example"]["comoving_projection_ratio"],
        )

    def test_next_requirements_forbid_raw_solder_map_as_lensing_amplitude(self) -> None:
        requirements = " ".join(build_payload()["next_requirements"])

        self.assertIn("Lorentz-admissible", requirements)
        self.assertIn("separate raw geometric soldering", requirements)
        self.assertIn("L_minus_to_plus=L_geom", requirements)
        self.assertIn("Bianchi K_plus/K_minus", requirements)


if __name__ == "__main__":
    unittest.main()
