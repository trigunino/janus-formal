from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_observable_chain_consistency_audit import build_payload


class ObservableChainConsistencyAuditTests(unittest.TestCase):
    def test_flags_resolution_report_that_does_not_cover_absolute_grid(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            absolute_path = root / "absolute.json"
            resolution_path = root / "resolution.json"
            absolute_path.write_text(
                json.dumps(
                    {
                        "grid": 175,
                        "finite": True,
                        "initial_state": "bounded_anticorrelated_gaussian_displacement_ic",
                    }
                ),
                encoding="utf-8",
            )
            resolution_path.write_text(
                json.dumps(
                    {
                        "grids": [128],
                        "max_grid": 128,
                        "required_grid_for_sigma8_radius": 175,
                        "max_relative_shear_change": 0.2,
                        "finite": True,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(absolute_path, resolution_path)

        self.assertTrue(payload["blocking_issue"])
        self.assertFalse(payload["checks"]["resolution_report_covers_absolute_grid"])
        self.assertEqual(payload["existing_absolute_run"]["grid"], 175)
        self.assertIn("--grids 128,175", payload["needed_command"])
        self.assertIn("--ic-family bounded-gaussian", payload["needed_command"])

    def test_flags_grid_covered_but_unstable_amplitude(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            absolute_path = root / "absolute.json"
            resolution_path = root / "resolution.json"
            absolute_path.write_text(
                json.dumps({"grid": 175, "finite": True}),
                encoding="utf-8",
            )
            resolution_path.write_text(
                json.dumps(
                    {
                        "grids": [96, 128, 175],
                        "max_grid": 175,
                        "required_grid_for_sigma8_radius": 175,
                        "max_relative_shear_change": 8.0,
                        "finite": True,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload(absolute_path, resolution_path)

        self.assertTrue(payload["blocking_issue"])
        self.assertFalse(payload["checks"]["amplitude_resolution_stable"])
        self.assertIn("absolute shear amplitude is not resolution-stable", payload["blockers"])


if __name__ == "__main__":
    unittest.main()
