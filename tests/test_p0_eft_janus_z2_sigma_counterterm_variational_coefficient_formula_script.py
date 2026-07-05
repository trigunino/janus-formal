import unittest

from scripts.derive_p0_eft_janus_z2_sigma_counterterm_variational_coefficient_formula import (
    build_payload,
)


class CountertermVariationalCoefficientFormulaTests(unittest.TestCase):
    def test_derives_measure_aware_formulas_but_not_values(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["formula_derivation_closed"])
        self.assertTrue(payload["measure_variation_included"])
        self.assertFalse(payload["explicit_values_ready"])
        self.assertFalse(payload["counterterm_local_density_action_inputs_allowed"])
        self.assertIn("1/2 h^ab L_ct", payload["formulas"]["R_h_ab"])
        self.assertEqual(payload["formulas"]["R_K_ab"], "-partial L_ct/partial K_ab")
        self.assertEqual(payload["primary_blocker"], "explicit_L_ct_expression")


if __name__ == "__main__":
    unittest.main()
