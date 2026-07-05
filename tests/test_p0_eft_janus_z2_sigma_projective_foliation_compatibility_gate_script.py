import unittest

from scripts.build_p0_eft_janus_z2_sigma_projective_foliation_compatibility_gate import (
    build_payload,
)


class ProjectiveFoliationCompatibilityGateTests(unittest.TestCase):
    def test_generic_s4_leaf_does_not_close_rp3_slice(self):
        payload = build_payload()

        self.assertTrue(payload["global_projective_cover_ready"])
        self.assertTrue(payload["antipodal_maps_generic_leaf_to_paired_leaf"])
        self.assertFalse(payload["generic_leaf_is_antipodal_invariant"])
        self.assertFalse(payload["single_leaf_RP3_inference_allowed"])
        self.assertFalse(payload["projective_foliation_inputs_writable"])
        self.assertFalse(payload["gate_passed"])

    def test_forbids_external_background_sources(self):
        payload = build_payload()

        self.assertFalse(payload["uses_compressed_planck_lcdm_background"])
        self.assertFalse(payload["uses_archived_z4_background"])
        self.assertFalse(payload["uses_observational_curvature_fit"])


if __name__ == "__main__":
    unittest.main()
