import unittest

from scripts.build_p0_eft_janus_z2_sigma_weakfield_poisson_interaction_sign_gate import (
    build_payload,
)


class WeakFieldPoissonInteractionSignGateTests(unittest.TestCase):
    def test_poisson_sign_matrix_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["poisson_system"]["matrix"], [[1.0, -1.0], [-1.0, 1.0]])
        self.assertTrue(payload["closure"]["plus_equation_source_signed"])
        self.assertTrue(payload["closure"]["minus_equation_source_signed"])

    def test_same_sector_attracts_and_cross_sector_repels(self):
        payload = build_payload()

        self.assertEqual(payload["interactions"]["plus_plus"], "attract")
        self.assertEqual(payload["interactions"]["minus_minus"], "attract")
        self.assertEqual(payload["interactions"]["plus_minus"], "repel")
        self.assertEqual(payload["interactions"]["minus_plus"], "repel")
        self.assertTrue(payload["closure"]["same_sector_attraction_derived"])
        self.assertTrue(payload["closure"]["cross_sector_repulsion_derived"])

    def test_gate_is_conditional_not_main_closure(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["conditional_only"])
        self.assertFalse(payload["feeds_main_branch"])
        self.assertIn("does_not_close_tensor_Bianchi", payload["non_closure"])
        self.assertIn("does_not_close_R_Sigma_solution_certificate", payload["non_closure"])


if __name__ == "__main__":
    unittest.main()
