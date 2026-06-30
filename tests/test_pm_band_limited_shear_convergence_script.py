from __future__ import annotations

import unittest

from scripts.build_pm_band_limited_shear_convergence import build_payload


def row(grid: int, powers: list[float]) -> dict:
    return {
        "grid": grid,
        "shear_power_bands": [
            {
                "k_center_inv_mpc": 0.01 * (index + 1),
                "power": power,
                "mode_count": 4,
            }
            for index, power in enumerate(powers)
        ],
    }


class PMBandLimitedShearConvergenceTests(unittest.TestCase):
    def test_reports_stable_common_band(self) -> None:
        payload = build_payload(
            {
                "grids": [4, 5, 6],
                "rows": [
                    row(4, [1.0, 10.0]),
                    row(5, [1.2, 50.0]),
                    row(6, [1.3, 200.0]),
                ],
            },
            max_relative_power_change=0.5,
        )

        self.assertFalse(payload["blocking_issue"])
        self.assertEqual(payload["stable_band_count"], 1)
        self.assertTrue(payload["bands"][0]["stable"])
        self.assertFalse(payload["bands"][1]["stable"])

    def test_blocks_when_no_band_is_stable(self) -> None:
        payload = build_payload(
            {
                "grids": [4, 5],
                "rows": [
                    row(4, [1.0]),
                    row(5, [3.0]),
                ],
            },
            max_relative_power_change=0.5,
        )

        self.assertTrue(payload["blocking_issue"])
        self.assertEqual(payload["stable_band_count"], 0)


if __name__ == "__main__":
    unittest.main()
