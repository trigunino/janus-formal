from __future__ import annotations

import unittest

from scripts.build_p0_dynamic_phi_l_selection_mirror_closure import build_payload


class P0DynamicPhiLSelectionMirrorClosureTests(unittest.TestCase):
    def test_mirror_closed_but_dynamic_selection_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "mirror-closed-dynamic-selection-open")
        self.assertFalse(payload["dynamic_phi_l_selection_closed"])
        self.assertTrue(payload["mirror_inverse_consistency_closed"])
        self.assertTrue(payload["single_cross_dust_mirror_cuu_closed"])
        self.assertTrue(payload["requires_new_axiom_or_source_action"])
        self.assertFalse(payload["prediction_ready"])

    def test_selection_rows_state_source_action_gap(self) -> None:
        rows = " ".join(row["claim"] for row in build_payload()["selection_rows"])

        self.assertIn("no unique phi/L variational action", rows)
        self.assertIn("formal map equations", rows)
        self.assertIn("not uniquely fixed", rows)
        self.assertIn("does not yet source-select", rows)

    def test_mirror_rows_include_inverse_l_determinant_and_cuu(self) -> None:
        rows = " ".join(row["identity"] for row in build_payload()["mirror_rows"])

        self.assertIn("phi_plus_to_minus o phi_minus_to_plus", rows)
        self.assertIn("L_plus_to_minus = L_minus_to_plus^{-1}", rows)
        self.assertIn("B_4vol_minus_to_plus * B_4vol_plus_to_minus = 1", rows)
        self.assertIn("C_minus-plus", rows)


if __name__ == "__main__":
    unittest.main()
