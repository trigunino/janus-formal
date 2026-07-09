import unittest

from janus_lab.janus_phase_space_occupation_search import (
    adiabatic_radiation_first_law_derivation_payload,
)


class JanusAdiabaticRadiationFirstLawGateTests(unittest.TestCase):
    def test_first_law_conditionally_derives_required_occupation(self):
        payload = adiabatic_radiation_first_law_derivation_payload()

        self.assertEqual(payload["derived_exponents"]["rho_gamma"], -4.0)
        self.assertEqual(payload["derived_exponents"]["bare_blackbody_n_gamma"], -6.0)
        self.assertEqual(payload["derived_exponents"]["target_conserved_n_gamma"], -3.0)
        self.assertEqual(payload["derived_exponents"]["required_occupation"], 3.0)
        self.assertTrue(payload["conditional_closure"])

    def test_remaining_obligations_are_not_hidden(self):
        payload = adiabatic_radiation_first_law_derivation_payload()

        self.assertIn(
            "prove the occupation multiplier is an actual phase-space/entropy density, not a post-hoc degeneracy",
            payload["remaining_non_rustine_proof_obligations"],
        )


if __name__ == "__main__":
    unittest.main()
