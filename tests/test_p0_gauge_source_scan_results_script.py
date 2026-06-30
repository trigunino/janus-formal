from __future__ import annotations

import unittest

from scripts.build_p0_gauge_source_scan_results import build_payload


class P0GaugeSourceScanResultsTests(unittest.TestCase):
    def test_scan_finds_no_source_closure(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["all_tracks_scanned"])
        self.assertFalse(payload["any_source_found"])
        self.assertIsNone(payload["accepted_branch"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_all_three_tracks_are_recorded(self) -> None:
        tracks = {row["track"] for row in build_payload()["scan_results"]}

        self.assertIn("Pi eigenframe", tracks)
        self.assertIn("boundary/initial L", tracks)
        self.assertIn("action/gauge principle", tracks)

    def test_decision_prioritizes_boundary_then_pi(self) -> None:
        decision = " ".join(build_payload()["decision"])

        self.assertIn("no current source closes", decision)
        self.assertIn("boundary/initial L remains first", decision)
        self.assertIn("Pi branch", decision)
        self.assertIn("action/gauge branch remains highest risk", decision)

    def test_next_steps_require_axiom_or_kinetic_moments(self) -> None:
        next_steps = " ".join(row["next"] for row in build_payload()["scan_results"])

        self.assertIn("kinetic/Vlasov", next_steps)
        self.assertIn("boundary axiom", next_steps)
        self.assertIn("new variational principle", next_steps)


if __name__ == "__main__":
    unittest.main()
