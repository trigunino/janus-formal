from __future__ import annotations

from argparse import Namespace
import unittest

from scripts.run_pm_qcross_absolute_shear_resolution import build_payload


class PMQCrossAbsoluteShearResolutionScriptTests(unittest.TestCase):
    def test_resolution_payload_compares_grids(self) -> None:
        payload = build_payload(
            Namespace(
                grids="4,5",
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
                displacement_scale=0.05,
                ic_family="analytic-multimode",
                mass_normalization="fixed-total",
            )
        )

        self.assertTrue(payload["finite"])
        self.assertEqual(payload["grids"], [4, 5])
        self.assertEqual(payload["run_settings"]["mass_normalization"], "fixed-total")
        self.assertGreater(payload["required_grid_for_sigma8_radius"], 5)
        self.assertIsNotNone(payload["rows"][1]["relative_shear_change_from_previous"])


if __name__ == "__main__":
    unittest.main()
