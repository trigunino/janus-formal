import unittest

from scripts.derive_p0_eft_janus_z2_sigma_no_extension_charge_normalization_no_go_gate import (
    build_payload,
)


class JanusZ2SigmaNoExtensionChargeNormalizationNoGoGateTest(unittest.TestCase):
    def test_no_extension_exhausted_at_absolute_charge_normalization(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(
            payload["primary_blocker"], "superselection_state_or_initial_occupation_not_fixed"
        )
        self.assertTrue(payload["facts"]["Z2_projection_weights_fixed"])
        self.assertEqual(
            payload["reduction"]["deck_invariant_projected_charge_formula"],
            "N_Z2Sigma = N_occ",
        )
        self.assertFalse(payload["policy"]["extension_allowed"])
        self.assertFalse(payload["policy"]["observational_baryon_fit_allowed"])
        self.assertFalse(payload["derivable_without_extra_input"]["absolute_N_Z2Sigma"])
        self.assertFalse(
            payload["derivable_without_extra_input"][
                "baryon_number_density0_m3_Z2Sigma"
            ]
        )
        self.assertTrue(
            payload["consequence"]["no_extension_route_exhausted_at_charge_normalization"]
        )
        self.assertTrue(
            payload["consequence"][
                "projected_charge_reduced_to_single_open_occupation"
            ]
        )
        self.assertTrue(
            payload["consequence"]["occupation_degeneracy_demonstrated"]
        )
        self.assertFalse(
            payload["occupation_degeneracy"]["topology_selects_unique_occupation"]
        )
        self.assertFalse(
            payload["consequence"]["early_plasma_baryon_density_no_extension_ready"]
        )
        self.assertFalse(payload["consequence"]["scale_free_BAO_primitive_ready"])


if __name__ == "__main__":
    unittest.main()
