import unittest

from janus_lab.janus_phase_space_occupation_search import (
    eq40_saha_ionization_scaling_payload,
)


class JanusEq40SahaIonizationScalingGateTests(unittest.TestCase):
    def test_saha_scaling_has_native_recombination_exponential(self):
        payload = eq40_saha_ionization_scaling_payload()

        self.assertEqual(payload["derived"]["thermal_prefactor_exponent"], -4.5)
        self.assertEqual(payload["derived"]["prefactor_over_baryon_exponent"], -1.5)
        self.assertEqual(payload["derived"]["exponential_argument"], "- const * a")
        self.assertTrue(payload["unblocks"]["native_ionization_visibility_law"])

    def test_absolute_anchor_still_required(self):
        payload = eq40_saha_ionization_scaling_payload()

        self.assertTrue(payload["unblocks"]["requires_absolute_eta_b_or_temperature_anchor"])
        self.assertIn("derive the dimensionless constant E_ion/T0 in Janus units", payload["remaining"])


if __name__ == "__main__":
    unittest.main()
