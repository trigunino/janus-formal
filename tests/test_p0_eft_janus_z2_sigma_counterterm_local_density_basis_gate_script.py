import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_local_density_basis_gate import build_payload


class P0EFTJanusZ2SigmaCountertermLocalDensityBasisGateTests(unittest.TestCase):
    def test_local_density_basis_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["counterterm_local_density_basis_ledger_declared"])
        self.assertIn("h_ab", payload["allowed_basis"])
        self.assertIn("new counterterm coefficient", payload["forbidden"])

    def test_local_density_expansion_remains_open(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["unique_counterterm_transported"])
        self.assertTrue(payload["closure"]["local_density_basis_complete"])
        self.assertFalse(payload["closure"]["L_ct_local_expansion_derived"])
        self.assertFalse(payload["counterterm_local_density_basis_ready"])
        self.assertIn("derive_explicit_L_ct_in_allowed_basis", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
