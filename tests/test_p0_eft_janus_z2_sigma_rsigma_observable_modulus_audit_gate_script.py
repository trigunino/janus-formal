import unittest

from scripts.derive_p0_eft_janus_z2_sigma_rsigma_observable_modulus_audit_gate import (
    build_payload,
)


class RSigmaObservableModulusAuditGateTests(unittest.TestCase):
    def test_full_pipeline_still_depends_on_radius(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["R_Sigma_modulus_open"])
        self.assertFalse(payload["full_observable_RSigma_cancellation_proved"])
        self.assertFalse(payload["flat_modulus_certificate_allowed_for_full_pipeline"])
        self.assertEqual(payload["primary_blocker"], "full_pipeline_still_depends_on_RSigma")

    def test_scale_free_branch_can_continue_without_extension(self):
        payload = build_payload()
        sectors = payload["sectors"]

        self.assertFalse(sectors["projective_topology"]["uses_R_Sigma"])
        self.assertFalse(sectors["scale_free_BAO_formulation"]["uses_R_Sigma"])
        self.assertTrue(payload["scale_free_branch_can_be_pursued_without_extension"])
        self.assertTrue(payload["official_dimensional_branch_requires_radius_or_scale_input"])


if __name__ == "__main__":
    unittest.main()
