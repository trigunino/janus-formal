import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_fermi_dirac_isotropy_gate import build_payload


class P0EFTJanusZ2SigmaDiracFermiDiracIsotropyGateTests(unittest.TestCase):
    def test_fermi_dirac_isotropy_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_fermi_dirac_isotropy_ledger_declared"])
        self.assertTrue(payload["declared"]["radial_energy_criterion_declared"])
        self.assertTrue(payload["declared"]["projection_preserves_isotropy_criterion_declared"])
        self.assertIn("occupation_pm", payload["formulas"])

    def test_fermi_dirac_isotropy_closure_remains_blocked(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_energy_radial_derived"])
        self.assertFalse(payload["closure"]["projected_momentum_isotropy_derived"])
        self.assertFalse(payload["dirac_fermi_dirac_isotropy_ready"])
        self.assertIn("pass_Dirac_radial_energy_dispersion_gate", payload["next_required"])
        self.assertIn("pass_radial_occupation_projection_gate", payload["next_required"])
        self.assertIn("feed_result_to_distribution_isotropy_anisotropic_stress_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
