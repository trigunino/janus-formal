from __future__ import annotations

from argparse import Namespace
import unittest

from scripts.run_pm_qcross_absolute_shear import build_payload


class PMQCrossAbsoluteShearScriptTests(unittest.TestCase):
    def test_absolute_shear_payload_is_finite(self) -> None:
        payload = build_payload(
            Namespace(
                grid=4,
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
        self.assertEqual(payload["initial_state"], "analytic-multimode_displacement_ic")
        self.assertEqual(payload["mass_normalization"], "fixed-total")
        self.assertGreater(payload["coefficient_max"], 0.0)
        self.assertGreaterEqual(payload["shear_abs_rms"], 0.0)
        self.assertGreater(payload["source_metrics"]["lensing_contrast_rms"], 0.0)


if __name__ == "__main__":
    unittest.main()
