from __future__ import annotations

import csv
import json
import subprocess
import sys
import unittest
from pathlib import Path


class PowerObservablesScriptTests(unittest.TestCase):
    def test_power_observables_script_writes_three_fields(self) -> None:
        subprocess.run(
            [sys.executable, "scripts/analyze_cosmological_pm_power_observables.py"],
            check=True,
        )
        csv_path = Path("outputs/reports/cosmological_pm_power_observables.csv")

        with csv_path.open("r", encoding="utf-8") as handle:
            fields = {row["field"] for row in csv.DictReader(handle)}

        self.assertEqual(fields, {"positive", "negative", "signed"})
        json_path = Path("outputs/reports/cosmological_pm_power_observables.json")
        payload = json.loads(json_path.read_text(encoding="utf-8"))
        self.assertEqual(len(payload["signed_power_growth"]), 5)

    def test_physical_3d_power_script_writes_positive_band_powers(self) -> None:
        subprocess.run(
            [sys.executable, "scripts/analyze_cosmological_pm_3d_physical_power.py"],
            check=True,
        )
        csv_path = Path("outputs/reports/cosmological_pm_3d_physical_power.csv")

        with csv_path.open("r", encoding="utf-8") as handle:
            rows = list(csv.DictReader(handle))

        self.assertEqual({row["field"] for row in rows}, {"positive", "negative", "signed"})
        signed_rows = [row for row in rows if row["field"] == "signed"]
        self.assertEqual(len(signed_rows), 4)
        self.assertTrue(all(float(row["final_power_mpc3"]) > 0.0 for row in signed_rows))


if __name__ == "__main__":
    unittest.main()
