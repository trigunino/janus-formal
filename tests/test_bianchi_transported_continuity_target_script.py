from __future__ import annotations

import unittest

from scripts.build_bianchi_transported_continuity_target import build_payload


class BianchiTransportedContinuityTargetTests(unittest.TestCase):
    def test_target_equations_are_written_and_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["target_equations_written"])
        self.assertTrue(payload["product_rule_expanded"])
        self.assertFalse(payload["source_derived"])
        self.assertFalse(payload["residuals_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_contains_required_transport_equations(self) -> None:
        equations = build_payload()["target_equations"]

        self.assertIn("D_minus_nu(rho_minus u_-to+^nu)=0", equations)
        self.assertIn("D_plus_nu(rho_plus u_+to-^nu)=0", equations)

    def test_product_rule_keeps_density_and_velocity_terms_separate(self) -> None:
        expansion = " ".join(build_payload()["product_rule_expansion"])

        self.assertIn("u_-to+^nu D_minus_nu rho_minus", expansion)
        self.assertIn("rho_minus D_minus_nu u_-to+^nu", expansion)
        self.assertIn("u_+to-^nu D_plus_nu rho_plus", expansion)
        self.assertIn("rho_plus D_plus_nu u_+to-^nu", expansion)

    def test_dependencies_require_qdet_l_map_and_volume_convention(self) -> None:
        payload = build_payload()
        dependencies = " ".join(payload["dependencies"])

        self.assertTrue(payload["depends_on_qdet_density_measure"])
        self.assertTrue(payload["requires_l_map"])
        self.assertTrue(payload["requires_volume_convention"])
        self.assertIn("Q_det", dependencies)
        self.assertIn("L_minus_to_plus", dependencies)
        self.assertIn("volume convention", dependencies)

    def test_same_sector_continuity_is_not_enough(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["same_sector_continuity_sufficient"])
        self.assertIn("Same-sector continuity is insufficient", payload["insufficiency_statement"])
        self.assertIn("preserve the flux", payload["insufficiency_statement"])

    def test_forbidden_shortcuts_prevent_notational_closure(self) -> None:
        shortcuts = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("same-sector continuity", shortcuts)
        self.assertIn("raw determinant", shortcuts)
        self.assertIn("Bianchi residuals", shortcuts)


if __name__ == "__main__":
    unittest.main()
