from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_p0_flrw_relative_curvature_rows_target import (
    build_payload,
    curvature_symbols,
    derive_relative_rows,
)


class P0FlrwRelativeCurvatureRowsTargetTests(unittest.TestCase):
    def test_sympy_rows_match_flrw_orthonormal_differences(self) -> None:
        H_plus, H_minus, dH_plus, dH_minus = curvature_symbols()
        rows = derive_relative_rows()

        expected_i0 = (dH_minus + H_minus**2) - (dH_plus + H_plus**2)
        expected_ij = H_minus**2 - H_plus**2

        self.assertEqual(sp.simplify(rows["F_i0"] - expected_i0), 0)
        self.assertEqual(sp.simplify(rows["F_ij"] - expected_ij), 0)

    def test_payload_is_target_only_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "homogeneous-flrw-relative-curvature-target")
        self.assertTrue(payload["source_curvature_rows_computable"])
        self.assertFalse(payload["full_physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertEqual(payload["fit_parameters"], [])

    def test_scope_explicitly_excludes_full_janus_perturbation(self) -> None:
        payload = build_payload()

        self.assertIn("homogeneous FLRW target only", payload["scope"])
        self.assertIn("not full Janus perturbation", payload["scope"])
        self.assertIn("Bianchi-minimal", payload["description"])
        self.assertEqual(payload["feeds"], "p0_bianchi_minimal_curvature_numeric_probe")

    def test_curvature_row_definitions_are_reported(self) -> None:
        rows = {row["row"]: row for row in build_payload()["curvature_rows"]}

        self.assertEqual(
            rows["F_i0"]["definition"],
            "(dH_minus + H_minus**2) - (dH_plus + H_plus**2)",
        )
        self.assertEqual(rows["F_ij"]["definition"], "H_minus**2 - H_plus**2")
        self.assertIn("dH_minus", rows["F_i0"]["derived_expression"])
        self.assertIn("H_minus**2", rows["F_ij"]["derived_expression"])


if __name__ == "__main__":
    unittest.main()
