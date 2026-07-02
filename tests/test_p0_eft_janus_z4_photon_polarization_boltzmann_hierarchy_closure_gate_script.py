import unittest

from scripts.build_p0_eft_janus_z4_photon_polarization_boltzmann_hierarchy_closure_gate import (
    LMAX_VALUES,
    build_payload,
)


class P0EFTJanusZ4PhotonPolarizationBoltzmannHierarchyClosureGateTests(unittest.TestCase):
    def test_photon_polarization_hierarchy_closure(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-photon-polarization-boltzmann-hierarchy-closure-gate")
        self.assertTrue(payload["scalar_mode_only"])
        self.assertTrue(payload["B_modes_disabled_or_GR_only"])
        self.assertEqual(payload["lmax_values"], list(LMAX_VALUES))
        self.assertTrue(payload["collision_terms_declared"])
        self.assertEqual(payload["opacity_rate_used"], "frozen_GR_visibility_backend")
        self.assertTrue(payload["Pi_source_derived_from_multipoles"])
        self.assertFalse(payload["Theta2_free_source_tag"])
        self.assertFalse(payload["direct_EE_patch"])
        self.assertFalse(payload["direct_TE_patch"])
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertFalse(payload["recombination_delta_enabled"])
        self.assertFalse(payload["visibility_delta_enabled"])
        self.assertFalse(payload["background_projection_changed"])
        self.assertFalse(payload["r_s_changed"])
        self.assertFalse(payload["r_d_changed"])
        self.assertFalse(payload["primordial_delta_enabled"])
        self.assertTrue(payload["lensing_C_phi_phi_frozen"])
        self.assertTrue(payload["slip_frozen"])
        self.assertTrue(payload["tight_coupling_regime_declared"])
        self.assertTrue(payload["transition_regime_declared"])
        self.assertTrue(payload["free_streaming_regime_declared"])
        self.assertTrue(payload["TCA_switch_smoothness_passed"])
        self.assertTrue(payload["strong_TCA_suppression_passed"])
        self.assertTrue(payload["lmax_convergence_passed"])
        self.assertEqual(payload["photon_polarization_hierarchy_status"], "boltzmann_hierarchy_closed_effective")
        self.assertTrue(payload["photon_polarization_boltzmann_hierarchy_closure_gate_passed"])
        self.assertFalse(payload["full_planck_verdict"])


if __name__ == "__main__":
    unittest.main()
