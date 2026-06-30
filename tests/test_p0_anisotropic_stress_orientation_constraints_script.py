from __future__ import annotations

import unittest

from scripts.build_p0_anisotropic_stress_orientation_constraints import build_payload


class P0AnisotropicStressOrientationConstraintsTests(unittest.TestCase):
    def test_pi_can_constrain_orientation_but_is_not_closed(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["pi_can_fix_orientation_when_nondegenerate"])
        self.assertFalse(payload["pi_evolution_source_derived"])
        self.assertFalse(payload["full_rotation_fixed_generically"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_pi_tensor_constraints_are_preserved(self) -> None:
        constraints = " ".join(build_payload()["tensor_constraints"])

        self.assertIn("Pi^{AB}=Pi^{BA}", constraints)
        self.assertIn("eta_AB Pi^{AB}=0", constraints)
        self.assertIn("Pi^{AB}u_B=0", constraints)
        self.assertIn("orthogonality", constraints)

    def test_orientation_depends_on_pi_eigenstructure(self) -> None:
        roles = {row["case"]: row for row in build_payload()["orientation_role"]}

        self.assertIn("rest-space rotations remain", roles["Pi=0"]["effect_on_f"])
        self.assertIn("principal axes", roles["Pi has distinct spatial eigenvalues"]["orientation_information"])
        self.assertIn("degenerate subspaces remain", roles["Pi has degenerate eigenvalues"]["effect_on_f"])

    def test_transport_equations_use_same_l_and_include_dpi(self) -> None:
        equations = " ".join(build_payload()["transport_equations"])

        self.assertIn("L_minus_to_plus", equations)
        self.assertIn("D Pi_-to+", equations)
        self.assertIn("K_minus", equations)
        self.assertIn("L_plus_to_minus", equations)

    def test_pi_cannot_be_used_to_overfit_orientation(self) -> None:
        text = " ".join(build_payload()["f_constraints_from_pi"] + build_payload()["still_open"])

        self.assertIn("source-derived", text)
        self.assertIn("overfit orientation", text)
        self.assertIn("Pi=0 or degenerate", text)


if __name__ == "__main__":
    unittest.main()
