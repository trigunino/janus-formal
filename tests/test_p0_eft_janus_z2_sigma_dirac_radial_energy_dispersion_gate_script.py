import unittest

from scripts.build_p0_eft_janus_z2_sigma_dirac_radial_energy_dispersion_gate import build_payload


class P0EFTJanusZ2SigmaDiracRadialEnergyDispersionGateTests(unittest.TestCase):
    def test_radial_energy_dispersion_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dirac_radial_energy_dispersion_ledger_declared"])
        self.assertTrue(payload["declared"]["comoving_momentum_redshift_declared"])
        self.assertTrue(payload["declared"]["scalar_mass_law_criterion_declared"])
        self.assertIn("epsilon_pm", payload["formulas"])

    def test_radial_energy_dispersion_closure_remains_blocked(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_scalar_mass_derived"])
        self.assertFalse(payload["closure"]["projected_radial_energy_derived"])
        self.assertFalse(payload["dirac_radial_energy_dispersion_ready"])
        self.assertIn("pass_Dirac_scalar_mass_law_gate", payload["next_required"])
        self.assertIn("pass_FLRW_momentum_frame_gate", payload["next_required"])
        self.assertIn("feed_result_to_Dirac_Fermi_Dirac_isotropy_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
