from __future__ import annotations

import unittest

from janus_lab.kink_growth import growth_prediction_ready, integrate_kink_growth


class KinkGrowthTests(unittest.TestCase):
    def test_kink_jump_is_not_applied_without_derived_coefficient(self) -> None:
        rows = integrate_kink_growth(
            k=1.0,
            a_initial=0.2,
            a_final=1.0,
            a_sigma=0.5,
            s_kink=lambda _k, _a: 10.0,
            skink_coefficient_derived=False,
            samples=32,
        )

        self.assertTrue(any(row["jump_applied"] for row in rows))
        self.assertLess(rows[-1]["ddelta_dln_a"], 1.0)

    def test_kink_jump_changes_growth_velocity_when_enabled(self) -> None:
        disabled = integrate_kink_growth(
            k=1.0,
            a_initial=0.2,
            a_final=1.0,
            a_sigma=0.5,
            s_kink=lambda _k, _a: 0.1,
            skink_coefficient_derived=False,
            samples=64,
        )
        enabled = integrate_kink_growth(
            k=1.0,
            a_initial=0.2,
            a_final=1.0,
            a_sigma=0.5,
            s_kink=lambda _k, _a: 0.1,
            skink_coefficient_derived=True,
            samples=64,
        )

        self.assertAlmostEqual(disabled[0]["delta"], enabled[0]["delta"])
        self.assertGreater(enabled[-1]["ddelta_dln_a"], disabled[-1]["ddelta_dln_a"])

    def test_prediction_ready_requires_both_source_closures(self) -> None:
        self.assertFalse(growth_prediction_ready(skink_coefficient_derived=True, alpha_janus_derived=False))
        self.assertTrue(growth_prediction_ready(skink_coefficient_derived=True, alpha_janus_derived=True))


if __name__ == "__main__":
    unittest.main()
