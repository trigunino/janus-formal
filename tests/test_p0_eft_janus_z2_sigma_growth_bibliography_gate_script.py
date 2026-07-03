import unittest

from scripts.build_p0_eft_janus_z2_sigma_growth_bibliography_gate import build_payload


class P0EFTJanusZ2SigmaGrowthBibliographyGateTests(unittest.TestCase):
    def test_bibliography_requires_local_growth_derivation(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["standard_linear_perturbation_source_found"])
        self.assertTrue(payload["bimetric_perturbation_source_found"])
        self.assertTrue(payload["einstein_cartan_perturbation_source_found"])
        self.assertTrue(payload["janus_structure_growth_source_found"])
        self.assertFalse(payload["complete_z2_sigma_growth_equations_found"])
        self.assertTrue(payload["local_growth_derivation_required"])
        self.assertTrue(payload["must_derive_z2_sigma_mu_slip_friction_locally"])


if __name__ == "__main__":
    unittest.main()
