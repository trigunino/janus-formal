from __future__ import annotations

import unittest

from scripts.build_p0_eft_delta_neff_denominator_bao_score import build_payload


class P0EFTDeltaNeffDenominatorBAOScoreTests(unittest.TestCase):
    def test_denominator_bao_score_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "delta-neff-denominator-bao-score-computed")
        self.assertGreater(len(payload["rows"]), 1)
        self.assertIn("best", payload)

    def test_denominator_48_is_scored_not_declared_derived(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["is_derived_geometry"])
        self.assertIn("48", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
