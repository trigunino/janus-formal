import unittest

from scripts.write_p0_eft_janus_z2_global_bimetric_mass_state_input import (
    build_payload,
)


class GlobalBimetricMassStateInputScriptTests(unittest.TestCase):
    def test_valid_global_mass_state_payload(self):
        payload = build_payload(
            m_plus_kg=3.0,
            provenance="active_bimetric_noether_state_charge",
        )

        self.assertEqual(payload["M_plus_kg"], 3.0)
        self.assertEqual(payload["M_minus_kg"], -3.0)
        self.assertTrue(payload["PT_energy_sign_reversal_proved"])
        self.assertTrue(payload["bimetric_global_solution_proved"])
        self.assertFalse(payload["observational_fit_used"])

    def test_invalid_or_observational_provenance_is_rejected(self):
        with self.assertRaises(ValueError):
            build_payload(m_plus_kg=0.0, provenance="state")
        with self.assertRaises(ValueError):
            build_payload(m_plus_kg=1.0, provenance="Planck fit")


if __name__ == "__main__":
    unittest.main()
