import unittest

from scripts.build_p0_eft_janus_topology_layer_alignment_gate import build_payload


class P0EFTJanusTopologyLayerAlignmentGateTests(unittest.TestCase):
    def test_projective_cover_is_z2_not_cyclic_z4(self):
        payload = build_payload()

        self.assertEqual(payload["projective_topology"]["global_topology"], "S4_to_RP4_antipodal_quotient")
        self.assertEqual(payload["projective_topology"]["cover_group"], "Z2")
        self.assertTrue(payload["projective_topology"]["two_fold_cover_derived"])
        self.assertTrue(payload["projective_topology"]["big_bang_pole_defined"])
        self.assertTrue(payload["projective_topology"]["big_crunch_pole_defined"])
        self.assertTrue(payload["projective_topology"]["antipodal_poles_coincide"])
        self.assertFalse(payload["projective_topology"]["antipodal_quotient_singular_orbifold"])
        self.assertFalse(payload["projective_topology"]["cyclic_z4_derived_from_cover"])
        self.assertTrue(payload["topological_z2_cover_does_not_imply_cyclic_z4"])

    def test_tunnel_surgery_is_separate_from_free_quotient(self):
        payload = build_payload()

        self.assertTrue(payload["tunnel_surgery"]["initial_singularities_present"])
        self.assertTrue(payload["tunnel_surgery"]["big_bang_big_crunch_coincidence"])
        self.assertTrue(payload["tunnel_surgery"]["tubular_replacement_defined"])
        self.assertTrue(payload["tunnel_surgery"]["tunnel_connects_two_folds"])
        self.assertTrue(payload["tunnel_surgery"]["singularities_removed_by_tunnel"])
        self.assertTrue(payload["tunnel_surgery"]["tunnel_layer_separate_from_free_quotient"])

    def test_four_sector_packaging_requires_order_four_monodromy(self):
        payload = build_payload()

        self.assertEqual(payload["four_sector_symmetry"]["natural_four_sector_group"], "Z2xZ2")
        self.assertFalse(payload["four_sector_symmetry"]["cyclic_z4_monodromy_proved"])
        self.assertFalse(payload["four_sector_symmetry"]["cyclic_z4_inference_allowed"])
        self.assertIn("prove_order4_monodromy_before_cyclic_Z4_claim", payload["next_required"])

    def test_pin_minus_must_be_rechecked_for_rp4(self):
        payload = build_payload()

        self.assertTrue(payload["aps_pin_impact"]["rp4_pin_sign_recheck_required"])
        self.assertTrue(payload["aps_pin_impact"]["pin_minus_not_promoted_from_boy_shadow_to_rp4"])


if __name__ == "__main__":
    unittest.main()
