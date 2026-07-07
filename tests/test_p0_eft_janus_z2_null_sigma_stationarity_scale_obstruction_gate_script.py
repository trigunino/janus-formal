import unittest

from scripts.build_p0_eft_janus_z2_null_sigma_stationarity_scale_obstruction_gate import (
    build_payload,
)


class NullSigmaStationarityScaleObstructionGateTests(unittest.TestCase):
    def test_null_stationarity_does_not_select_absolute_rs(self):
        payload = build_payload()

        self.assertEqual(payload["branch"], "Z2_null_Sigma_PT_bridge")
        self.assertEqual(payload["radial_density_coefficient_over_sin_theta"], 0.5)
        self.assertTrue(payload["closure"]["PT_stress_slots_available"])
        self.assertTrue(payload["closure"]["generator_rescaling_fixed"])
        self.assertFalse(payload["closure"]["radial_stationarity_equation_sets_finite_Rs"])
        self.assertFalse(payload["null_stationarity_selects_absolute_Rs"])
        self.assertIn("no internal length scale", payload["obstruction"])


if __name__ == "__main__":
    unittest.main()
