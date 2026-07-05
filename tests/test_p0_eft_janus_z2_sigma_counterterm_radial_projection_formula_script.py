import unittest

from scripts.derive_p0_eft_janus_z2_sigma_counterterm_radial_projection_formula import (
    build_payload,
)


class P0EFTJanusZ2SigmaCountertermRadialProjectionFormulaTests(unittest.TestCase):
    def test_projects_symbolic_primitive_to_radial_formula(self):
        payload = build_payload()
        formula = payload["formula"]

        self.assertTrue(payload["gate_passed"])
        self.assertIn("partial_R L_ct", formula["radial_derivative"])
        self.assertEqual(
            formula["reduced_radial_derivative"],
            "partial_R L_ct = -(2 R_Sigma R_h^{ab} q_ab + R_K^{ab} q_ab + R_chi partial_R chi)",
        )
        self.assertIn("E_counterterm = partial_R", formula["E_counterterm_formula"])
        self.assertFalse(formula["value_profile_ready"])
        self.assertIn("R_h^{ab} q_ab", formula["still_requires_for_values"])


if __name__ == "__main__":
    unittest.main()
