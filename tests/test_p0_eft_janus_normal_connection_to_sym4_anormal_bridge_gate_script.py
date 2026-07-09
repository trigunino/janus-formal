import unittest

from janus_lab.janus_phase_space_occupation_search import (
    normal_connection_to_sym4_anormal_bridge_payload,
)


class JanusNormalConnectionToSym4AnormalBridgeGateTests(unittest.TestCase):
    def test_calculator_exists_but_active_manifest_is_missing(self):
        payload = normal_connection_to_sym4_anormal_bridge_payload()
        machinery = payload["existing_normal_connection_machinery"]

        self.assertTrue(machinery["calculator_ready"])
        self.assertFalse(machinery["active_input_manifest_present"])
        self.assertFalse(machinery["normal_connection_ready_now"])

    def test_rho_perp_to_c11_is_required(self):
        payload = normal_connection_to_sym4_anormal_bridge_payload()

        self.assertFalse(payload["bridge_requirements"]["rho_perp_to_End_C11_derived"])
        self.assertFalse(payload["bridge_requirements"]["A_normal_on_C11_defined"])
        self.assertEqual(payload["if_bridge_closes"]["z_max"], 1000.0)
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
