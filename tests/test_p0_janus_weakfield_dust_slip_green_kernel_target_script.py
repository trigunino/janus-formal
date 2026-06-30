from __future__ import annotations

import unittest

from scripts.build_p0_janus_weakfield_dust_slip_green_kernel_target import (
    build_payload,
    determinant,
    render_markdown,
    solve_mode,
    source_compatibility,
)


class P0JanusWeakfieldDustSlipGreenKernelTargetTests(unittest.TestCase):
    def test_determinant_matches_fourier_gate_factor(self) -> None:
        self.assertEqual(determinant(5.0, 1.0, 2.0, 3.0), 4.0 * 5.0 * (5.0 + 2.0 - 3.0))

    def test_zero_mode_requires_source_compatibility(self) -> None:
        self.assertEqual(source_compatibility(4.0, -6.0, 2.0, 3.0), 0.0)
        failed = solve_mode(0.0, 1.0, 2.0, 3.0, 1.0, 1.0)

        self.assertFalse(failed["solvable"])
        self.assertEqual(failed["reason"], "source_compatibility_failed")

    def test_compatible_zero_mode_fixes_common_gauge_only(self) -> None:
        solved = solve_mode(0.0, 1.0, 2.0, 3.0, 4.0, -6.0)

        self.assertTrue(solved["solvable"])
        self.assertEqual(solved["reason"], "common_mode_gauge_fixed")
        self.assertAlmostEqual(solved["psi_plus"] + solved["psi_minus"], 0.0)

    def test_finite_modes_invert_or_block_resonance(self) -> None:
        solved = solve_mode(5.0, 1.0, 2.0, 3.0, 4.0, -1.0)
        blocked = solve_mode(1.0, 1.0, 2.0, 3.0, 4.0, -1.0)

        self.assertTrue(solved["solvable"])
        self.assertEqual(solved["reason"], "finite_mode_inverted")
        self.assertFalse(blocked["solvable"])
        self.assertEqual(blocked["reason"], "mass_gap_resonance")

    def test_payload_is_diagnostic_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dust-slip-green-kernel-target-open")
        self.assertTrue(payload["green_kernel_written"])
        self.assertTrue(payload["zero_mode_policy_written"])
        self.assertTrue(payload["resonance_policy_written"])
        self.assertFalse(payload["background_branch_selected"])
        self.assertFalse(payload["qdet_convention_selected_from_source"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_lists_no_prediction_gate(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("mass-gap resonance blocks", markdown)


if __name__ == "__main__":
    unittest.main()
