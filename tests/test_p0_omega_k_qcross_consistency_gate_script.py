from __future__ import annotations

import unittest

from scripts.build_p0_omega_k_qcross_consistency_gate import build_payload, render_markdown


class P0OmegaKQCrossConsistencyGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "omega-k-qcross-consistency-open")
        self.assertTrue(payload["same_l_omega_required"])
        self.assertFalse(payload["k_only_omega_choice_allowed"])
        self.assertTrue(payload["mirror_inverse_required"])
        self.assertTrue(payload["optical_projection_compatibility_required"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_consistency_rows_cover_required_checks(self) -> None:
        rows = {row["gate"]: row for row in build_payload()["consistency_rows"]}

        self.assertIn("shared_l_omega", rows)
        self.assertIn("no_k_only_cancellation", rows)
        self.assertIn("mirror_inverse", rows)
        self.assertIn("optical_projection_compatibility", rows)
        self.assertTrue(all(not row["closed"] for row in rows.values()))

    def test_omega_cannot_be_chosen_to_cancel_k_only(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("choose Omega to cancel K transport only", forbidden)
        self.assertIn("different L/Omega", forbidden)
        self.assertIn("scalar Q_cross or Q_det", forbidden)

    def test_prediction_requires_same_omega_mirror_and_optics(self) -> None:
        requirements = " ".join(build_payload()["prediction_requirements"])

        self.assertIn("same L/Omega", requirements)
        self.assertIn("mirror inverse", requirements)
        self.assertIn("K_plus and K_minus residual closure", requirements)
        self.assertIn("Q_cross optical projection compatibility", requirements)

    def test_markdown_renders_gate_table_and_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("| gate | requirement | closed |", markdown)
        self.assertIn("K-only Omega choice allowed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
