import unittest

from scripts.build_p0_eft_janus_z2_sigma_cmb_boltzmann_bibliography_gate import build_payload


class P0EFTJanusZ2SigmaCMBBoltzmannBibliographyGateTests(unittest.TestCase):
    def test_bibliography_requires_local_cmb_derivation(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["ma_bertschinger_source_found"])
        self.assertTrue(payload["camb_class_source_found"])
        self.assertTrue(payload["photon_polarization_hierarchy_source_found"])
        self.assertFalse(payload["complete_z2_sigma_cmb_boltzmann_equations_found"])
        self.assertTrue(payload["local_cmb_derivation_required"])
        self.assertTrue(payload["must_derive_z2_sigma_metric_sources_locally"])


if __name__ == "__main__":
    unittest.main()
