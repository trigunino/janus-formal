from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_polarization_hierarchy_closure import build_payload as build_pol, write_reports as write_pol
from scripts.build_p0_eft_janus_z4_scalar_swisw_closure import build_payload as build_scalar, write_reports as write_scalar
from scripts.build_p0_eft_janus_z4_weyl_lensing_projection_closure import build_payload as build_lensing, write_reports as write_lensing


class P0EFTJanusZ4PhysicalClosureAuditsScriptTests(unittest.TestCase):
    def test_polarization_closure_audit_is_symbolic_not_claimed(self) -> None:
        payload = build_pol()

        self.assertTrue(payload["symbolic_audit_ready"])
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["polarization_hierarchy_physical_ready"])
        self.assertTrue(payload["unique_algebraic_solution"])
        self.assertTrue(payload["algebraic_closure_verified"])
        self.assertEqual(payload["upstream_required_flag"], "coefficientsFromFullZ4Action")
        self.assertIn("phase_closure_residual", payload["residuals"])
        self.assertTrue(all(value == "0" for value in payload["residuals_after_substitution"].values()))

    def test_scalar_swisw_closure_audit_is_symbolic_not_claimed(self) -> None:
        payload = build_scalar()

        self.assertTrue(payload["symbolic_audit_ready"])
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["scalar_swisw_physical_ready"])
        self.assertTrue(payload["conditional_partial_closure_verified"])
        self.assertIn("a_P", payload["conditional_targets"])
        self.assertEqual(payload["upstream_required_flag"], "scalarActionDerivedReady")
        self.assertIn("isw_source", payload["residuals"])

    def test_lensing_projection_closure_audit_is_symbolic_not_claimed(self) -> None:
        payload = build_lensing()

        self.assertTrue(payload["symbolic_audit_ready"])
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["lensing_projection_physical_ready"])
        self.assertTrue(payload["unique_algebraic_solution"])
        self.assertTrue(payload["algebraic_projection_verified"])
        self.assertEqual(payload["upstream_required_flag"], "sourceCoefficientsDerived")
        self.assertIn("kernel_residual", payload["residuals"])
        self.assertTrue(all(value == "0" for value in payload["residuals_after_substitution"].values()))

    def test_report_writers_export_outputs(self) -> None:
        write_pol()
        write_scalar()
        write_lensing()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_polarization_hierarchy_closure.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_scalar_swisw_closure.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_weyl_lensing_projection_closure.json").exists())


if __name__ == "__main__":
    unittest.main()
