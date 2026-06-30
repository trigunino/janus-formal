from __future__ import annotations

import unittest

from scripts.build_p0_k_interaction_tensor_candidate_families import build_payload


class P0KInteractionTensorCandidateFamiliesTests(unittest.TestCase):
    def test_artifact_is_p0_open_and_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "p0-open")
        self.assertFalse(payload["prediction_ready"])

    def test_required_families_are_classified(self) -> None:
        rows = {row["family"]: row for row in build_payload()["families"]}

        self.assertEqual(rows["naive_copied_stress"]["classification"], "rejected")
        self.assertEqual(rows["determinant_weighted_copied_stress"]["classification"], "rejected")
        self.assertEqual(rows["lorentz_transported_dust"]["classification"], "candidate")
        self.assertEqual(rows["perfect_fluid_transported_tensor"]["classification"], "candidate")
        self.assertEqual(rows["anisotropic_transported_tensor"]["classification"], "candidate")
        self.assertEqual(rows["bianchi_solved_k_pde"]["classification"], "diagnostic")

    def test_scalar_qdet_qcross_absorption_is_forbidden(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_shortcuts"])
        verdict = build_payload()["verdict"]

        self.assertIn("scalar Q_det", forbidden)
        self.assertIn("scalar Q_cross", forbidden)
        self.assertIn("scalar Qdet/Qcross", forbidden)
        self.assertIn("Scalar Qdet/Qcross absorption is forbidden", verdict)

    def test_candidates_require_bianchi_and_qcross_consistency(self) -> None:
        checks = " ".join(build_payload()["required_next_checks"])

        self.assertIn("R_plus^mu=R_minus^mu=0", checks)
        self.assertIn("Q_cross optical projection", checks)
        self.assertIn("source-derived candidate tensors", checks)


if __name__ == "__main__":
    unittest.main()
