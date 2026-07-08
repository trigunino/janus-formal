import unittest

from scripts.build_p0_eft_janus_complex_reality_coadjoint_state_space_gate import (
    build_payload,
)


class ComplexRealityCoadjointStateSpaceGateTests(unittest.TestCase):
    def test_complex_state_space_is_ready_without_alpha_law(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["complex_coadjoint_state_space_ready"])
        self.assertFalse(payload["alpha_generated_now"])
        self.assertEqual(payload["next_gate"], "ComplexRealityKKSBoundaryDensityGate")
        self.assertIn("complex_state_space_scaffold", payload["what_this_closes"])
        self.assertIn("KKS_two_form_on_boundary_orbit_derived", payload["what_remains"])

    def test_state_space_declares_kks_safe_translation_policy(self):
        payload = build_payload()

        self.assertTrue(payload["checks"]["antihermitian_translation_projection_declared"])
        self.assertEqual(
            payload["state_space"]["coadjoint_translation_policy"],
            "antihermitian_projection_required_for_KKS",
        )


if __name__ == "__main__":
    unittest.main()
