import unittest

from janus_lab.janus_phase_space_occupation_search import (
    eq40_photon_clock_transport_audit_payload,
)


class JanusEq40PhotonClockTransportAuditGateTests(unittest.TestCase):
    def test_minimal_photon_clock_transport_does_not_support_s4(self):
        payload = eq40_photon_clock_transport_audit_payload()

        self.assertEqual(payload["derived_exponents"]["inferred_one_plus_z"], 0.5)
        self.assertFalse(payload["result"]["supports_s4"])
        self.assertFalse(payload["result"]["produces_high_power_redshift"])

    def test_audit_remains_diagnostic_until_conventions_fixed(self):
        payload = eq40_photon_clock_transport_audit_payload()

        self.assertTrue(payload["result"]["diagnostic_only"])
        self.assertIn("check whether the Janus source defines redshift geometrically", payload["remaining"][0])


if __name__ == "__main__":
    unittest.main()
