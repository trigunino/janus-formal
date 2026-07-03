import unittest

from scripts.build_p0_eft_janus_z2_sigma_growth_perturbation_equation_gate import build_payload


class P0EFTJanusZ2SigmaGrowthPerturbationEquationGateTests(unittest.TestCase):
    def test_growth_perturbation_equations_are_derived_without_z4_mu_reuse(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["growth_perturbation_lock_closed"])
        self.assertTrue(payload["growth_perturbation_equations_derived"])
        self.assertTrue(payload["lock"]["z2_sigma_poisson_constraint_derived"])
        self.assertTrue(payload["lock"]["z2_sigma_slip_relation_derived"])
        self.assertTrue(payload["archived_z4_mu_reuse_forbidden"])
        self.assertTrue(payload["non_compressed_growth_gate_ready"])


if __name__ == "__main__":
    unittest.main()
