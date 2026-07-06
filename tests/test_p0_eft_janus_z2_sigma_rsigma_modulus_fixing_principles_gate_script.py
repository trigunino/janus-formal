import unittest

from scripts.derive_p0_eft_janus_z2_sigma_rsigma_modulus_fixing_principles_gate import (
    build_payload,
)


class RSigmaModulusFixingPrinciplesGateTests(unittest.TestCase):
    def test_known_internal_principles_do_not_fix_radius(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["R_Sigma_modulus_open"])
        self.assertFalse(payload["fixed_by_known_internal_principle"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_modulus_open")

    def test_topology_and_sqrt_counterterm_are_not_radius_laws(self):
        payload = build_payload()
        principles = payload["principles"]

        self.assertFalse(principles["projective_Z2_topology"]["fixes_R_Sigma"])
        self.assertFalse(
            principles["sqrt_intrinsic_curvature_counterterm"]["fixes_R_Sigma"]
        )
        self.assertFalse(principles["core_tension_plus_intrinsic_R"]["fixes_R_Sigma"])
        self.assertFalse(principles["existing_formal_action"]["fixes_R_Sigma"])
        self.assertFalse(principles["surface_intrinsic_curvature_policy"]["fixes_R_Sigma"])
        self.assertIn("C/B", payload["next_physical_inputs"][0])


if __name__ == "__main__":
    unittest.main()
