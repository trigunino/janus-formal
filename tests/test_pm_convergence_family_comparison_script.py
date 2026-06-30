from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.build_pm_convergence_family_comparison import build_payload


class PMConvergenceFamilyComparisonTests(unittest.TestCase):
    def test_controlled_analytic_fixed_total_can_be_marked_ready(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            bounded = root / "bounded.json"
            analytic = root / "analytic.json"
            bounded.write_text(
                json.dumps(
                    {
                        "run_settings": {"ic_family": "bounded-gaussian"},
                        "stable_band_count": 0,
                        "common_band_count": 6,
                        "blocking_issue": True,
                    }
                ),
                encoding="utf-8",
            )
            analytic.write_text(
                json.dumps(
                    {
                        "run_settings": {
                            "ic_family": "analytic-multimode",
                            "mass_normalization": "fixed-total",
                        },
                        "stable_band_count": 6,
                        "common_band_count": 6,
                        "blocking_issue": False,
                    }
                ),
                encoding="utf-8",
            )

            payload = build_payload([bounded, analytic])

        self.assertTrue(payload["controlled_numerical_convergence_ready"])
        self.assertIn("Numerical convergence only", payload["boundary"])


if __name__ == "__main__":
    unittest.main()
