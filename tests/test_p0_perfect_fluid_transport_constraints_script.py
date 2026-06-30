from __future__ import annotations

import unittest

from scripts.build_p0_perfect_fluid_transport_constraints import build_payload


class P0PerfectFluidTransportConstraintsTests(unittest.TestCase):
    def test_perfect_fluid_adds_constraints_but_does_not_close_physics(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["pressure_constraints_added"])
        self.assertTrue(payload["projector_constraints_added"])
        self.assertFalse(payload["source_derived_w_cross"])
        self.assertFalse(payload["pure_rotation_fixed"])
        self.assertFalse(payload["full_l_transport_fixed"])
        self.assertFalse(payload["prediction_ready"])

    def test_stress_forms_include_dust_and_perfect_fluid(self) -> None:
        forms = " ".join(build_payload()["stress_forms"])

        self.assertIn("dust", forms)
        self.assertIn("(rho+p)u^A u^B+p eta^{AB}", forms)
        self.assertIn("h^{AB}=eta^{AB}+u^A u^B", forms)

    def test_added_constraints_include_pressure_projector_and_eos(self) -> None:
        terms = {row["term"] for row in build_payload()["added_constraints"]}
        effects = " ".join(row["effect_on_f"] for row in build_payload()["added_constraints"])

        self.assertIn("pressure_gradient", terms)
        self.assertIn("projector_derivative", terms)
        self.assertIn("equation_of_state", terms)
        self.assertIn("isotropic rest-space force", effects)
        self.assertIn("rotation-invariant", effects)

    def test_isotropic_pressure_leaves_rotations_free(self) -> None:
        free = " ".join(build_payload()["still_free_components"])
        upgrade = " ".join(build_payload()["closure_upgrade"])

        self.assertIn("pure spatial rotation", free)
        self.assertIn("screen-plane rotations", free)
        self.assertIn("anisotropic stress", upgrade)

    def test_forbids_scalar_absorption_and_fits(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("do not choose w_cross by fitting", forbidden)
        self.assertIn("scalar Q_det", forbidden)
        self.assertIn("scalar Q_cross", forbidden)
        self.assertIn("FLRW scalar", forbidden)


if __name__ == "__main__":
    unittest.main()
