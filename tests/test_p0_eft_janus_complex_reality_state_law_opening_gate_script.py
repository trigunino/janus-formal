import unittest

from scripts.build_p0_eft_janus_complex_reality_state_law_opening_gate import (
    build_payload,
)


class ComplexRealityStateLawOpeningGateTests(unittest.TestCase):
    def test_branch_is_opened_without_claiming_alpha(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["branch_opened"])
        self.assertEqual(payload["conceptual_branch"], "janus_complex_reality_state_law")
        self.assertEqual(payload["source_anchor"], "X2026-complex-reality")
        self.assertFalse(payload["alpha_generated_now"])
        self.assertFalse(payload["observational_branch_opened"])
        self.assertIn("alpha_fixed_now", payload["forbidden_claims"])

    def test_plan_targets_the_known_alpha_blockers(self):
        payload = build_payload()

        self.assertIn(
            "derive_or_reject_nonzero_kks_boundary_density",
            payload["objectives"],
        )
        self.assertIn("test_prequantization_integrality", payload["objectives"])
        self.assertIn(
            "nonzero_KKS_or_boundary_symplectic_density_not_yet_derived",
            payload["current_blockers"],
        )
        self.assertEqual(payload["next_gate"], "ComplexRealitySourceFormulaCurationGate")


if __name__ == "__main__":
    unittest.main()
