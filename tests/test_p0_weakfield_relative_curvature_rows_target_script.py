from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_p0_weakfield_relative_curvature_rows_target import (
    build_payload,
    derive_relative_rows,
    potential_differences,
    potential_symbols,
    spatial_hessian_symbols,
)


class P0WeakfieldRelativeCurvatureRowsTargetTests(unittest.TestCase):
    def test_sympy_temporal_rows_match_phi_hessian_difference(self) -> None:
        hessians = spatial_hessian_symbols()
        rows = derive_relative_rows()["temporal_tidal_rows"]

        expected = hessians["Phi_minus"][("x", "y")] - hessians["Phi_plus"][("x", "y")]
        self.assertEqual(sp.simplify(rows["Delta_R_0x0y"] - expected), 0)
        self.assertEqual(
            rows["Delta_R_0x0y"],
            rows["Delta_R_0y0x"] if "Delta_R_0y0x" in rows else rows["Delta_R_0x0y"],
        )

    def test_sympy_spatial_rows_match_psi_hessian_difference(self) -> None:
        hessians = spatial_hessian_symbols()
        rows = derive_relative_rows()["spatial_tidal_rows"]

        delta_xx = hessians["Psi_minus"][("x", "x")] - hessians["Psi_plus"][("x", "x")]
        delta_yy = hessians["Psi_minus"][("y", "y")] - hessians["Psi_plus"][("y", "y")]
        delta_yz = hessians["Psi_minus"][("y", "z")] - hessians["Psi_plus"][("y", "z")]

        self.assertEqual(sp.simplify(rows["Delta_R_xyxy"] - (delta_xx + delta_yy)), 0)
        self.assertEqual(sp.simplify(rows["Delta_R_xyxz"] - delta_yz), 0)

    def test_potential_placeholders_and_differences_are_reported(self) -> None:
        Phi_plus, Phi_minus, Psi_plus, Psi_minus = potential_symbols()
        differences = potential_differences()
        payload = build_payload()

        self.assertEqual(sp.simplify(differences["Delta_Phi"] - (Phi_minus - Phi_plus)), 0)
        self.assertEqual(sp.simplify(differences["Delta_Psi"] - (Psi_minus - Psi_plus)), 0)
        self.assertEqual(
            payload["potential_symbols"],
            ["Phi_plus", "Phi_minus", "Psi_plus", "Psi_minus"],
        )
        self.assertIn("H_Phi_minus_xy", payload["hessian_symbols"])
        self.assertIn("H_Psi_plus_zz", payload["hessian_symbols"])

    def test_payload_is_restricted_target_only_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "restricted-weakfield-relative-curvature-target")
        self.assertTrue(payload["source_rows_computable"])
        self.assertTrue(payload["source_curvature_rows_computable"])
        self.assertFalse(payload["full_physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertEqual(payload["fit_parameters"], [])

    def test_scope_and_feeds_are_curvature_integrability_only(self) -> None:
        payload = build_payload()
        rows = {row["row"]: row for row in payload["curvature_rows"]}

        self.assertIn("restricted Newtonian-gauge/weak-field target only", payload["scope"])
        self.assertIn("not full Janus perturbation or tetrad closure", payload["scope"])
        self.assertIn("p0_curvature_integrability_sparse_pde_probe", payload["feeds"])
        self.assertIn("Hessian(Phi_minus - Phi_plus)", rows["Delta_R_0x0x"]["definition"])
        self.assertIn("Hessian(Psi_minus - Psi_plus)", rows["Delta_R_xyxy"]["definition"])


if __name__ == "__main__":
    unittest.main()
