from __future__ import annotations

import unittest

from scripts.build_p0_bianchi_closure_candidate_criteria import build_payload


class P0BianchiClosureCandidateCriteriaTests(unittest.TestCase):
    def test_required_acceptance_criteria_are_present(self) -> None:
        payload = build_payload()
        criteria = " ".join(
            f"{row['criterion']} {row['accept']}" for row in payload["criteria"]
        )

        self.assertIn("R_plus^mu=0 after substituting", criteria)
        self.assertIn("R_minus^mu=0 after substituting", criteria)
        self.assertIn("same L_minus_to_plus/L_plus_to_minus", criteria)
        self.assertIn("Q_cross", criteria)
        self.assertIn("Q_det/proper-density/sign convention", criteria)
        self.assertIn("pressure and anisotropic-stress Pi divergence", criteria)
        self.assertIn("no fitted amplitudes", criteria)
        self.assertIn("Newtonian weak-field and TOV/static-fluid limits", criteria)
        self.assertIn("accepted source anchors", criteria)

    def test_prediction_ready_requires_every_criterion_true(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["all_criteria_true"])
        self.assertFalse(payload["prediction_ready"])
        self.assertEqual(
            payload["prediction_ready"],
            all(row["satisfied"] for row in payload["criteria"]),
        )

    def test_rejects_flrw_only_and_newtonian_only_candidates(self) -> None:
        reject_reasons = " ".join(build_payload()["reject_reasons"])

        self.assertIn("only close FLRW", reject_reasons)
        self.assertIn("only recover Newtonian", reject_reasons)
        self.assertIn("omitting pressure or Pi divergence", reject_reasons)
        self.assertIn("different L maps", reject_reasons)


if __name__ == "__main__":
    unittest.main()
