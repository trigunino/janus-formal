import unittest

from scripts.build_p0_eft_janus_z2_sigma_cmb_boltzmann_equation_gate import build_payload


class P0EFTJanusZ2SigmaCMBBoltzmannEquationGateTests(unittest.TestCase):
    def test_cmb_boltzmann_equations_are_derived_without_archived_z4_reuse(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["cmb_boltzmann_lock_closed"])
        self.assertTrue(payload["cmb_boltzmann_equations_derived"])
        self.assertTrue(payload["lock"]["photon_temperature_hierarchy_declared"])
        self.assertTrue(payload["lock"]["photon_polarization_hierarchy_declared"])
        self.assertTrue(payload["lock"]["z2_sigma_metric_source_terms_derived"])
        self.assertTrue(payload["archived_z4_cmb_reuse_forbidden"])
        self.assertTrue(payload["non_compressed_cmb_gate_ready"])


if __name__ == "__main__":
    unittest.main()
