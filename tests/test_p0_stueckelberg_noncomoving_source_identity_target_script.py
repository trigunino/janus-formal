from __future__ import annotations

import unittest

from scripts.build_p0_stueckelberg_noncomoving_source_identity_target import build_payload


class P0NoncomovingSourceIdentityTargetTests(unittest.TestCase):
    def test_target_defined_but_not_closed(self) -> None:
        payload = build_payload()
        decision = payload["decision"]

        self.assertTrue(decision["boosted_t00_formula_checked"])
        self.assertTrue(decision["noncomoving_source_identity_target_defined"])
        self.assertTrue(decision["local_gamma_u_t00_code_available"])
        self.assertTrue(decision["beta_field_provenance_gate_available"])
        self.assertFalse(decision["source_derived_beta_available"])
        self.assertFalse(decision["noncomoving_source_identity_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_formula_contains_boosted_pressure_pi_and_limits(self) -> None:
        formula = " ".join(build_payload()["formula"].values())

        self.assertIn("gamma^2", formula)
        self.assertIn("-p+Pi00", formula)
        self.assertIn("rho gamma^2", formula)
        self.assertIn("T00=rho", formula)

    def test_requirements_block_scalar_absorption(self) -> None:
        requirements = " ".join(build_payload()["closure_requirements"])

        self.assertIn("source-derived gamma field", requirements)
        self.assertIn("pressure/equation-of-state", requirements)
        self.assertIn("Pi00 transport", requirements)
        self.assertIn("not as scalar absorption", requirements)
        self.assertIn("T0i", requirements)

    def test_code_surfaces_include_gamma_u_and_t00_helpers(self) -> None:
        surfaces = " ".join(build_payload()["code_surfaces"])

        self.assertIn("lorentz_gamma_from_beta_vectors", surfaces)
        self.assertIn("transported_four_velocity_from_beta_vectors", surfaces)
        self.assertIn("boosted_perfect_fluid_t00_source", surfaces)
        self.assertIn("positive_noncomoving_t00_source_grid", surfaces)
        self.assertIn("beta_field_provenance_gate", surfaces)


if __name__ == "__main__":
    unittest.main()
