import unittest

from janus_lab.janus_phase_space_occupation_search import (
    variable_constants_thermal_frame_map_payload,
)


class JanusVariableConstantsThermalFrameMapGateTests(unittest.TestCase):
    def test_thermal_frame_exponents_are_solved(self):
        payload = variable_constants_thermal_frame_map_payload()

        self.assertEqual(payload["solution"]["thermal_energy_temperature_exponent"], -1.0)
        self.assertEqual(payload["solution"]["occupation_exponent"], 3.0)
        self.assertEqual(payload["solution"]["n_gamma_exponent"], -3.0)
        self.assertEqual(payload["solution"]["rho_gamma_exponent"], -4.0)
        self.assertTrue(all(payload["checks"].values()))

    def test_remaining_blockers_are_real_plasma_inputs(self):
        payload = variable_constants_thermal_frame_map_payload()

        self.assertIn("derive active baryon density", payload["remaining"])
        self.assertIn("derive pre-drag H_J(a)", payload["remaining"])


if __name__ == "__main__":
    unittest.main()
