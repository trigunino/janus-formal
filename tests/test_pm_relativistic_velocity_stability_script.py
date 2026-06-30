from __future__ import annotations

from argparse import Namespace
import unittest

from scripts.diagnose_pm_relativistic_velocity_stability import build_payload


class PMRelativisticVelocityStabilityScriptTests(unittest.TestCase):
    def test_stability_scan_reports_valid_rows(self) -> None:
        payload = build_payload(
            Namespace(
                grids="4",
                displacement_scales="0.001",
                steps=3,
                dt=0.0001,
                gravity_scale=0.5,
                box_size_mpc=1000.0,
                h0=70.0,
                omega_abs=0.315,
                q0=-0.087,
                source_redshifts="0.8,1.2",
                source_weights="",
                axis=2,
                seed=123,
                shape_amplitude=1.0,
                ic_family="analytic-multimode",
            )
        )

        self.assertEqual(payload["valid_count"], 1)
        self.assertEqual(payload["invalid_count"], 0)


if __name__ == "__main__":
    unittest.main()
