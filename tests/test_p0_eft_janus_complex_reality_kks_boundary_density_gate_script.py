import unittest

from scripts.build_p0_eft_janus_complex_reality_kks_boundary_density_gate import (
    build_payload,
)


class ComplexRealityKKSBoundaryDensityGateTests(unittest.TestCase):
    def test_global_kks_is_nonzero_but_boundary_density_is_not_ready(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["global_KKS_orbit_nonzero"])
        self.assertFalse(payload["KKS_boundary_density_ready"])
        self.assertFalse(payload["KKS_boundary_density_nonzero"])
        self.assertFalse(payload["alpha_generated_now"])

    def test_boundary_blockers_are_explicit(self):
        payload = build_payload()

        self.assertIn("sigma_boundary_phase_space_declared", payload["current_blockers"])
        self.assertIn(
            "sigma_variations_mapped_to_complex_lie_algebra",
            payload["current_blockers"],
        )
        self.assertIn(
            "boundary_two_cycle_with_nonzero_period_declared",
            payload["current_blockers"],
        )
        self.assertEqual(payload["next_gate"], "ComplexRealitySigmaBoundaryProjectionGate")


if __name__ == "__main__":
    unittest.main()
