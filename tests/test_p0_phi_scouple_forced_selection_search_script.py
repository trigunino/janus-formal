from __future__ import annotations

import unittest

from scripts.build_p0_phi_scouple_forced_selection_search import build_payload


class P0PhiScoupleForcedSelectionSearchTests(unittest.TestCase):
    def test_no_track_forces_unique_phi_scouple(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "forced-selection-not-found")
        self.assertFalse(payload["split_noether_forces_unique"])
        self.assertFalse(payload["limits_force_unique"])
        self.assertFalse(payload["invariants_force_unique"])
        self.assertFalse(payload["unique_phi_scouple_forced"])
        self.assertTrue(payload["family_obstruction_confirmed"])
        self.assertFalse(payload["prediction_ready"])

    def test_tracks_cover_noether_limits_and_invariants(self) -> None:
        tracks = {row["track"]: row for row in build_payload()["investigation_tracks"]}

        self.assertIn("split_noether", tracks)
        self.assertIn("flrw_newtonian_tov_limits", tracks)
        self.assertIn("invariant_classification", tracks)
        self.assertTrue(all(not row["forces_unique"] for row in tracks.values()))

    def test_candidate_family_and_closure_conditions_remain_explicit(self) -> None:
        payload = build_payload()
        family = " ".join(payload["remaining_candidate_family"])
        needed = " ".join(payload["closure_conditions_needed"])

        self.assertIn("I_matter", family)
        self.assertIn("F(I_metric, I_matter)", family)
        self.assertIn("split Noether", needed)
        self.assertIn("pressure/Pi", needed)


if __name__ == "__main__":
    unittest.main()
