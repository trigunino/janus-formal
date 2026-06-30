from __future__ import annotations

from argparse import Namespace
import unittest

from scripts.build_pm_time_lensing_normalization_calibration import build_payload


class PMTimeLensingNormalizationCalibrationTests(unittest.TestCase):
    def test_payload_closes_working_hubble_time_and_lensing_prefactor(self) -> None:
        payload = build_payload(
            Namespace(
                h0=70.0,
                box_size_mpc=1000.0,
                omega_abs=0.315,
                q0=-0.087,
                z_slices=32,
                source_redshifts="0.8,1.2",
                source_weights="",
            )
        )

        self.assertEqual(payload["pm_time_unit_basis"], "H0^-1")
        self.assertAlmostEqual(payload["pm_velocity_unit_km_s"], 70000.0, places=6)
        self.assertAlmostEqual(
            payload["tensor_prefactor_unity_branch"],
            payload["base_prefactor"],
        )
        self.assertGreater(payload["coefficient_max"], 0.0)


if __name__ == "__main__":
    unittest.main()
