from __future__ import annotations

import unittest

from scripts.build_p0_nonlocal_kernel_scouple_selector_obstruction import (
    build_payload,
    render_markdown,
)


class P0NonlocalKernelScoupleSelectorObstructionTests(unittest.TestCase):
    def test_invertible_kernel_selects_given_target_but_not_source_derived(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "nonlocal-kernel-scouple-selector-obstruction-open")
        self.assertEqual(payload["invertible_kernel_determinant"], "3")
        self.assertTrue(payload["nonlocal_kernel_can_select_given_target"])
        self.assertIn("{phi1: f1, phi2: f2}", payload["invertible_solution"])
        self.assertFalse(payload["nonlocal_route_selects_source_derived_phi_j_l"])

    def test_zero_mode_kernel_leaves_homogeneous_freedom(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["null_kernel_rank"], 1)
        self.assertEqual(payload["null_kernel_nullity"], 1)
        self.assertTrue(payload["null_kernel_zero_mode_exists"])

    def test_source_obligations_and_hidden_axiom_risk_remain(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["arbitrary_target_hiding_risk"])
        self.assertFalse(payload["kernel_source_derived"])
        self.assertFalse(payload["target_source_derived"])
        self.assertFalse(payload["causal_boundary_prescription_source_derived"])
        self.assertTrue(payload["requires_source_kernel"])
        self.assertTrue(payload["requires_source_target_or_current"])
        self.assertTrue(payload["requires_causal_boundary_prescription"])
        self.assertTrue(payload["requires_mirror_inverse_proof"])
        self.assertTrue(payload["requires_same_l_tensor_residual_proof"])
        self.assertTrue(payload["requires_split_noether_proof"])

    def test_zero_rustine_guards_and_markdown(self) -> None:
        payload = build_payload()
        markdown = render_markdown(payload)

        self.assertTrue(payload["new_axiom_if_adopted_without_source"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["hidden_axiom_used"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertIn("Arbitrary target hiding risk: True", markdown)
        self.assertIn("Nonlocal route selects source-derived phi/J/L: False", markdown)


if __name__ == "__main__":
    unittest.main()
