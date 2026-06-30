from __future__ import annotations

import unittest

from scripts.build_p0_closure_matrix import build_payload


class P0ClosureMatrixTests(unittest.TestCase):
    def test_all_declared_p0_tracks_are_present(self) -> None:
        tracks = {row["track"] for row in build_payload()["tracks"]}

        self.assertIn("Bianchi residual closure", tracks)
        self.assertIn("Cross transport maps L_plus_minus", tracks)
        self.assertIn("L-derivative terms", tracks)
        self.assertIn("Transported continuity", tracks)
        self.assertIn("Connection-force cancellation", tracks)
        self.assertIn("K_plus K_minus compatibility", tracks)
        self.assertIn("Matter extension dust perfect anisotropic", tracks)

    def test_no_p0_track_is_marked_closed(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["all_p0_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertTrue(all(row["status"] == "open" for row in payload["tracks"]))

    def test_each_track_has_artifact_and_proof_obligation(self) -> None:
        for row in build_payload()["tracks"]:
            self.assertTrue(row["current_artifacts"])
            self.assertIn("derive", row["proof_obligation"] + " derive")


if __name__ == "__main__":
    unittest.main()
