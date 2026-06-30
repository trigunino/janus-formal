from __future__ import annotations

import unittest

from scripts.build_remaining_scaffolds_roadmap import build_payload


class RemainingScaffoldsRoadmapTests(unittest.TestCase):
    def test_roadmap_tracks_all_blocking_scaffolds(self) -> None:
        payload = build_payload()
        tracks = {row["track"] for row in payload["tracks"]}

        self.assertIn("Bianchi closure", tracks)
        self.assertIn("Q_det", tracks)
        self.assertIn("Q_cross", tracks)
        self.assertIn("Survey layer", tracks)
        self.assertIn("Metric potential / Weyl", tracks)

    def test_metric_potential_track_blocks_lensing_promotion(self) -> None:
        track = next(
            row for row in build_payload()["tracks"] if row["track"] == "Metric potential / Weyl"
        )

        self.assertIn("Poisson/Weyl diagnostic", track["current"])
        self.assertIn("source-derived h_plus", track["replacement"])
        self.assertIn("S8_eff", track["blocks"])

    def test_roadmap_keeps_nonfit_normalization_map(self) -> None:
        payload = build_payload()

        self.assertTrue(any("factorized C_J" in item for item in payload["keepers"]))
        self.assertIn("parallel", payload["verdict"])


if __name__ == "__main__":
    unittest.main()
