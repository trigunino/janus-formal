import unittest

from scripts.build_p0_eft_janus_z2_published_bimetric_flrw_to_sigma_bridge_gate import (
    build_payload,
)


class PublishedBimetricFLRWToSigmaBridgeGateTests(unittest.TestCase):
    def test_bridge_declares_bulk_to_sigma_pipeline_without_shortcuts(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["strict_interpretation"]["sigma_is_bimetric_interface"])
        self.assertTrue(payload["strict_interpretation"]["bulk_source_must_pull_back_to_sigma"])
        self.assertFalse(payload["honest_bridge_ready"])
        self.assertFalse(payload["observable_E_Z2Sigma_a2_ready"])
        self.assertFalse(any(payload["honest_shortcuts_forbidden"].values()))

    def test_existing_flrw_reduction_is_not_enough_for_sigma_transport(self):
        payload = build_payload()

        self.assertTrue(payload["readiness"]["published_interaction_slots_ready"])
        self.assertTrue(payload["readiness"]["flrw_reduced_bianchi_ready"])
        self.assertTrue(payload["readiness"]["sector_rho_pressure_shape_ready"])
        self.assertFalse(payload["readiness"]["sector_rho_pressure_of_a_ready"])
        self.assertFalse(payload["readiness"]["sigma_embedding_pullback_ready"])
        self.assertIn("sector_rho_pressure_of_a_ready", payload["blockers"])

    def test_next_required_keeps_sigma_pullback_before_observables(self):
        payload = build_payload()

        self.assertIn(
            "derive active X_±(a) pullbacks h_± and K_± on Sigma",
            payload["next_required"],
        )
        self.assertIn("only then construct E_Z2Sigma(a)^2", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
